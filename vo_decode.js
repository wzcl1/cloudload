#!/usr/bin/env node
/*
 * VO (voe.sx / jamesbornmain.com) stream extractor.
 * Reads player HTML (argv[2] file path, or stdin), executes the inline scripts
 * inside a Node `vm` sandbox with browser + JWPlayer stubs, and captures the
 * real video file URL from the jwplayer load()/setup() config.
 *
 * Output: JSON { file, urls: [ ... ], player: {...} }
 */
'use strict';

const fs = require('fs');
const vm = require('vm');
const { TextEncoder, TextDecoder: RealTextDecoder } = require('util');

function readInput() {
  const arg = process.argv[2];
  if (arg && arg !== '-') return fs.readFileSync(arg, 'utf8');
  return fs.readFileSync(0, 'utf8');
}

// Player page URL (used to key the WASM decoder via location.hostname).
function readPageUrl() {
  return process.argv[3] || process.env.PLAYER_URL || 'https://jamesbornmain.com/e/unknown';
}

function extractInlineScripts(html) {
  const out = [];
  const re = /<script\b([^>]*)>([\s\S]*?)<\/script>/gi;
  let m;
  while ((m = re.exec(html)) !== null) {
    const attrs = m[1] || '';
    const body = m[2] || '';
    if (/\bsrc\s*=/i.test(attrs)) continue; // skip external
    if (!body.trim()) continue;
    out.push(body);
  }
  return out;
}

// ---- WASM-decoded URL capture --------------------------------------------
// VOE decodes the real stream URL inside a WebAssembly module and reads the
// result out of WASM memory with `new TextDecoder().decode(...)`. Wrapping
// TextDecoder.decode is the reliable capture point for the decoded URL.
const HTTP_RE = /^https?:\/\/\S+$/;
function makeCapturingTextDecoder(captured) {
  return class extends RealTextDecoder {
    decode(input, options) {
      const out = super.decode(input, options);
      if (typeof out === 'string') {
        const t = out.trim();
        captured.all_decodes.push(out);
        if (HTTP_RE.test(t)) captured.files.push(t);
      }
      return out;
    }
  };
}

// ---- Browser / JWPlayer stubs -------------------------------------------

function makeElement() {
  const el = {
    style: {},
    children: [],
    childNodes: [],
    dataset: {},
    attributes: {},
    innerHTML: '',
    innerText: '',
    textContent: '',
    value: '',
    parentNode: null,
    offsetWidth: 1024,
    offsetHeight: 768,
    clientWidth: 1024,
    clientHeight: 768,
    classList: {
      add() {}, remove() {}, toggle() {}, contains() { return false; },
    },
    setAttribute(k, v) { this.attributes[k] = v; this.dataset[k] = v; },
    getAttribute(k) { return this.attributes[k] != null ? this.attributes[k] : null; },
    removeAttribute() {},
    appendChild(c) { this.children.push(c); c.parentNode = this; return c; },
    removeChild(c) { const i = this.children.indexOf(c); if (i >= 0) this.children.splice(i, 1); return c; },
    insertBefore(c) { this.children.unshift(c); return c; },
    addEventListener() {},
    removeEventListener() {},
    querySelector() { return makeElement(); },
    querySelectorAll() { return []; },
    getElementsByTagName() { return [makeElement()]; },
    getElementsByClassName() { return []; },
    getBoundingClientRect() { return { top: 0, left: 0, width: 1024, height: 768, right: 1024, bottom: 768 }; },
    cloneNode() { return makeElement(); },
    focus() {}, blur() {}, click() {},
    contains() { return false; },
  };
  return el;
}

function buildSandbox(pageUrl) {
  const captured = { setups: [], loads: [], files: [], all_decodes: [], wasm: { inst: 0, exports: [] } };

  function recordConfig(cfg) {
    if (!cfg) return;
    if (typeof cfg.file === 'string') captured.files.push(cfg.file);
    if (cfg.sources && cfg.sources.length) {
      for (const s of cfg.sources) if (s && typeof s.file === 'string') captured.files.push(s.file);
    }
  }

  const player = {
    setup(cfg) { captured.setups.push(cfg); recordConfig(cfg); return player; },
    load(item) { captured.loads.push(item); recordConfig(item); return player; },
    on() { return player; },
    once() { return player; },
    off() { return player; },
    play() { return player; },
    pause() { return player; },
    stop() { return player; },
    seek() { return player; },
    resize() { return player; },
    addPlugin() { return player; },
    registerPlugin() { return player; },
    getContainer() { return makeElement(); },
    getSettings() { return {}; },
    setConfig(c) { recordConfig(c); return player; },
    getPlaylistIndex() { return 0; },
    getPlaylistItem() { return {}; },
    getDuration() { return 0; },
    getPosition() { return 0; },
    getVolume() { return 100; },
    setVolume() { return player; },
    mute() { return player; },
    unmute() { return player; },
    destroy() { return player; },
    key: '',
  };

  function jwplayer(id) { return player; }
  jwplayer.api = player;
  jwplayer.players = {};
  jwplayer.version = '8.49.5';
  jwplayer.key = '';

  const documentStub = {
    readyState: 'complete',
    cookie: '',
    referrer: pageUrl || '',
    title: '',
    body: makeElement(),
    head: makeElement(),
    documentElement: makeElement(),
    createElement: () => makeElement(),
    createTextNode: (t) => ({ textContent: t }),
    createDocumentFragment: () => makeElement(),
    getElementById: () => makeElement(),
    getElementsByTagName: () => [makeElement()],
    getElementsByClassName: () => [],
    querySelector: () => makeElement(),
    querySelectorAll: () => [],
    addEventListener() {},
    removeEventListener() {},
    write() {},
    writeln() {},
    execCommand() { return true; },
  };

  const storage = () => {
    const data = {};
    return {
      getItem: (k) => (k in data ? data[k] : null),
      setItem: (k, v) => { data[k] = String(v); },
      removeItem: (k) => { delete data[k]; },
      clear: () => { for (const k in data) delete data[k]; },
      key: () => null,
      get length() { return Object.keys(data).length; },
    };
  };

  const timers = [];
  const sandbox = {
    // captured (for the decoder to read back)
    __captured: captured,

    // constructors / globals
    console: { log() {}, warn() {}, error() {}, info() {}, debug() {}, trace() {}, clear() {} },
    Math, Date, JSON, Object, Array, String, Number, Boolean, RegExp, Error,
    TypeError, RangeError, SyntaxError, Promise, Symbol, Map, Set, WeakMap,
    parseInt, parseFloat, isNaN, isFinite,
    encodeURIComponent, decodeURIComponent, encodeURI, decodeURI, escape, unescape,
    NaN, Infinity, undefined,
    atob: (s) => Buffer.from(s, 'base64').toString('binary'),
    btoa: (s) => Buffer.from(s, 'binary').toString('base64'),

    // typed arrays / WASM memory support (required by the VOE WASM decoder)
    ArrayBuffer, SharedArrayBuffer, DataView,
    Int8Array, Uint8Array, Uint8ClampedArray, Int16Array, Uint16Array,
    Int32Array, Uint32Array, Float32Array, Float64Array,
    BigInt, BigInt64Array, BigUint64Array,
    TextEncoder,
    TextDecoder: makeCapturingTextDecoder(captured),
    WebAssembly: {
      instantiate: (bytes, imports) => WebAssembly.instantiate(bytes, imports).then((res) => {
        captured.wasm.inst += 1;
        const instance = res.instance || res;
        if (instance && instance.exports) {
          captured.wasm.exports.push(Object.keys(instance.exports));
        }
        return res;
      }),
      validate: WebAssembly.validate,
      Module: WebAssembly.Module,
      Instance: WebAssembly.Instance,
      Memory: WebAssembly.Memory,
    },

    // browser
    window: null, // set below (self)
    self: null,
    top: null,
    parent: null,
    document: documentStub,
    navigator: {
      userAgent: 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
      appVersion: '5.0 (Windows NT 10.0; Win64; x64)',
      platform: 'Win32',
      language: 'en-US',
      languages: ['en-US', 'en'],
      hardwareConcurrency: 8,
      maxTouchPoints: 0,
      cookieEnabled: true,
      onLine: true,
      vendor: 'Google Inc.',
      product: 'Gecko',
      productSub: '20030107',
    },
    location: (() => {
      const href = pageUrl || 'https://jamesbornmain.com/e/unknown';
      let u;
      try { u = new URL(href); } catch (e) { u = new URL('https://jamesbornmain.com/e/unknown'); }
      return {
        href: u.href,
        origin: u.origin,
        protocol: u.protocol,
        host: u.host,
        hostname: u.hostname,
        port: u.port,
        pathname: u.pathname,
        search: u.search,
        hash: u.hash,
        assign() {}, replace() {}, reload() {},
      };
    })(),
    history: { pushState() {}, replaceState() {}, back() {}, forward() {}, go() {}, length: 1 },
    screen: { width: 1920, height: 1080, availWidth: 1920, availHeight: 1040, colorDepth: 24, pixelDepth: 24 },
    innerWidth: 1024, innerHeight: 768, outerWidth: 1920, outerHeight: 1080,
    devicePixelRatio: 1,
    pageXOffset: 0, pageYOffset: 0, scrollX: 0, scrollY: 0,
    localStorage: storage(), sessionStorage: storage(),
    addEventListener() {}, removeEventListener() {},
    requestAnimationFrame: (cb) => { timers.push(cb); return timers.length; },
    cancelAnimationFrame() {},
    setTimeout: (cb, ms) => { timers.push(cb); return timers.length; },
    clearTimeout() {},
    setInterval: (cb, ms) => { timers.push(cb); return timers.length; },
    clearInterval() {},
    queueMicrotask: (cb) => { timers.push(cb); },
    fetch: () => Promise.resolve({ ok: true, status: 200, json: () => Promise.resolve({}), text: () => Promise.resolve('') }),
    XMLHttpRequest: function () {
      return {
        open() {}, send() {}, setRequestHeader() {}, abort() {},
        addEventListener() {}, responseText: '', response: '', status: 200, readyState: 4,
      };
    },
    Image: function () { return makeElement(); },
    Worker: function () { return { postMessage() {}, terminate() {}, addEventListener() {} }; },
    Audio: function () { return makeElement(); },
    MutationObserver: function () { return { observe() {}, disconnect() {}, takeRecords() { return []; } }; },
    IntersectionObserver: function () { return { observe() {}, unobserve() {}, disconnect() {} }; },
    PerformanceObserver: function () { return { observe() {}, disconnect() {} }; },
    performance: { now: () => Date.now(), timing: { navigationStart: Date.now() }, getEntriesByType: () => [] },
    CustomEvent: function (t, o) { return { type: t, ...(o || {}) }; },
    Event: function (t, o) { return { type: t, ...(o || {}) }; },
    KeyboardEvent: function (t, o) { return { type: t, ...(o || {}) }; },
    MouseEvent: function (t, o) { return { type: t, ...(o || {}) }; },
    URL: URL, URLSearchParams: URLSearchParams,
    atob, btoa,

    // player
    jwplayer,

    // catch-all for unknown globals is NOT possible in vm; rely on the above.
  };

  sandbox.window = sandbox;
  sandbox.self = sandbox;
  sandbox.top = sandbox;
  sandbox.parent = sandbox;

  return { sandbox, captured, timers };
}

async function main() {
  const html = readInput();
  const titleMatch = html.match(/<title[^>]*>([\s\S]*?)<\/title>/i);
  const scripts = extractInlineScripts(html);

  const pageUrl = readPageUrl();
  const { sandbox, captured, timers } = buildSandbox(pageUrl);
  const context = vm.createContext(sandbox);

  let errors = [];
  // Run scripts sequentially in the shared context; flush timers between.
  function flushTimers(rounds = 5) {
    for (let r = 0; r < rounds; r++) {
      const batch = timers.splice(0, timers.length);
      if (!batch.length) break;
      for (const cb of batch) {
        try { cb && cb(0); } catch (e) { /* ignore */ }
      }
    }
  }
  const sleep = (ms) => new Promise((r) => setImmediate(r));

  for (let si = 0; si < scripts.length; si++) {
    const s = scripts[si];
    try {
      vm.runInContext(s, context, { timeout: 5000 });
    } catch (e) {
      errors.push(`script[${si}]: ${String(e && e.message || e)}`);
    }
    flushTimers();
    // Yield to the real event loop so WASM instantiate / Promise.all settle.
    await sleep(0);
  }
  flushTimers(10);
  // Give the async decode chain (WebAssembly.instantiate -> Promise.all) time.
  for (let i = 0; i < 20 && !captured.files.length; i++) {
    await sleep(25);
    flushTimers(3);
  }

  // Gather candidate file URLs: WASM-decoded + any global strings.
  const urls = new Set(captured.files.filter(Boolean));
  let sourceUrl = null;
  try {
    for (const k of Object.keys(sandbox)) {
      const v = sandbox[k];
      if (typeof v === 'string' && /^https?:\/\//.test(v.trim())) {
        urls.add(v.trim());
        if (k === 'source' && !/test-videos|bigbuckbunny|sample\.|placeholder/i.test(v)) {
          sourceUrl = v.trim();
        }
      }
    }
  } catch (e) { /* ignore */ }

  // Rank: the resolved `source` global wins, then real (non-placeholder) URLs.
  const rank = (u) => {
    if (u === sourceUrl) return 100;
    if (/test-videos\.co\.uk|bigbuckbunny|sample\.|demo|placeholder/i.test(u)) return 0;
    if (/\.m3u8(\?|$)/i.test(u)) return 30;
    if (/\.mp4(\?|$)/i.test(u)) return 20;
    return 10;
  };
  const uniq = Array.from(urls);
  uniq.sort((a, b) => rank(b) - rank(a));
  const file = uniq[0] || null;

  const out = {
    title: titleMatch ? titleMatch[1].trim() : null,
    file,
    urls: uniq,
    setups: captured.setups.length,
    loads: captured.loads.length,
    errors: errors.slice(0, 8),
  };
  if (process.env.DEBUG) {
    out.debug = {
      script_count: scripts.length,
      source_url: (typeof sandbox.source === 'string') ? sandbox.source : null,
      staticBase: (typeof sandbox.staticBase === 'string') ? sandbox.staticBase : null,
      cdn_root: (typeof sandbox.cdn_root === 'string') ? sandbox.cdn_root : null,
      wasm: captured.wasm,
      decode_count: captured.all_decodes.length,
      decodes: captured.all_decodes.slice(0, 40).map((d) => (d.length > 200 ? d.slice(0, 200) + '…' : d)),
      globals_with_url: Object.keys(sandbox).filter((k) => {
        const v = sandbox[k];
        return typeof v === 'string' && /^https?:\/\//.test(v);
      }),
    };
  }
  process.stdout.write(JSON.stringify(out, null, 2) + '\n');
}

main().catch((e) => {
  process.stdout.write(JSON.stringify({ error: String(e && e.stack || e) }) + '\n');
  process.exit(1);
});
