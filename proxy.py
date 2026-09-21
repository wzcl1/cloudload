#!/usr/bin/env python3
"""
Jav.guru proxy server with ad stripping and video stream extractor.
Uses only Python stdlib. Download via yt-dlp.
"""

import base64
import concurrent.futures
import hashlib
import html
import hmac
import http.server
import json
import os
import random
import re
import shutil
import string
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from io import BytesIO

# ── Config ──────────────────────────────────────────────────────────────────
LISTEN_PORT = 8080
BASE_URL = "https://jav.guru"
DOWNLOAD_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "downloads")
YTDLP = os.environ.get("YTDLP", shutil.which("yt-dlp") or "yt-dlp")
ARIA2C = shutil.which("aria2c") or "aria2c"
MAX_DOWNLOADS = 3  # concurrent downloads
# Optional basic auth: set both to enable, leave either unset to disable.
BASIC_AUTH_USER = os.environ.get("BASIC_AUTH_USER", "")
BASIC_AUTH_PASS = os.environ.get("BASIC_AUTH_PASS", "")

os.makedirs(DOWNLOAD_DIR, exist_ok=True)

# Track active downloads: {id: {status, progress, file, title, error}}
downloads = {}
download_lock = threading.Lock()
download_procs = {}  # dl_id -> Popen (separate from downloads dict to avoid JSON issues)
download_counter = 0

# State lives in DOWNLOAD_DIR so it persists via the mounted volume.
STATE_FILE = os.path.join(DOWNLOAD_DIR, "downloads_state.json")


def save_state():
    """Persist download status to disk so it survives container restarts."""
    try:
        with download_lock:
            snapshot = {k: dict(v) for k, v in downloads.items()}
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(snapshot, f, indent=1)
        os.replace(tmp, STATE_FILE)
    except OSError:
        pass


def load_state():
    """Restore persisted download state.

    Downloads that were in flight when the server died become 'interrupted'
    (their partial files stay on disk, so they can be resumed)."""
    global download_counter
    if not os.path.exists(STATE_FILE):
        return
    try:
        with open(STATE_FILE) as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return
    for k, v in data.items():
        if not isinstance(v, dict):
            continue
        if v.get("status") in ("downloading", "queued"):
            v["status"] = "interrupted"
            v["progress"] = "Interrupted (server restarted)"
            v["error"] = None
            log_update(k, status="interrupted")
        downloads[k] = v
        try:
            download_counter = max(download_counter, int(k))
        except ValueError:
            pass
    save_state()


def _state_saver_loop():
    while True:
        time.sleep(10)
        save_state()


# ── Download log ────────────────────────────────────────────────────────────
# A permanent history of every download (title, provider, timestamps).
# Entries survive deletion from the downloads page.

LOG_FILE = os.path.join(DOWNLOAD_DIR, "download_log.json")
log_lock = threading.Lock()


def _load_log():
    try:
        with open(LOG_FILE) as f:
            data = json.load(f)
        return data if isinstance(data, list) else []
    except (OSError, json.JSONDecodeError):
        return []


def _save_log(log):
    tmp = LOG_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump(log, f, indent=1)
    os.replace(tmp, LOG_FILE)


def _now():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def log_add(dl_id, title, provider, resolution="", page_url=""):
    with log_lock:
        _save_log(_load_log() + [{
            "id": dl_id,
            "title": title,
            "provider": provider,
            "resolution": resolution,
            "page_url": page_url,
            "started": _now(),
            "finished": None,
            "status": "queued",
            "code": None,
        }])


def log_update(dl_id, **fields):
    """Update the newest log entry for a download id (status, code, ...).
    Pass finished=_now() explicitly for terminal states."""
    with log_lock:
        log = _load_log()
        for entry in reversed(log):
            if str(entry.get("id")) == str(dl_id):
                entry.update(fields)
                _save_log(log)
                return


load_state()

# ── Ad/Popup stripping patterns ─────────────────────────────────────────────
AD_DOMAINS = [
    "googletagmanager.com", "google-analytics.com", "googlesyndication.com",
    "doubleclick.net", "adskeeper.com", "propellerads.com", "pemsrv.com",
    "exoclick.com", "juicyads.com", "trafficjunky.com", "tsyndicate.com",
    "ad-maven.com", "a.pemsrv.com", "s.pemsrv.com", "go.godkc.com",
    "go.mayzaent.com", "fractionfridgejudiciary.com", "endedstrung.com",
    "purposeparking.com", "monkrix.com", "earnvids05032026.shop",
    "zm.acreageupwhirl.com", "5vbs96dea.com", "nn.toodlerehouse.com",
    "overplantovervaluetwine.com", "ruddy-pass.com", "xapi.juicyads.com",
    "emturbovid.com", "cloudflareinsights.com", "mc.yandex.ru",
    "ad.twinrdengine.com", "go.reebr.com",
]

AD_SCRIPT_PATTERNS = [
    r'popunder\d+\.js',
    r'adsbygoogle',
    r'adblock',
    r'_sp_',
    r'__gads',
    r'window\.open\s*\(',
    r'document\.write\s*\(\s*unescape',
    r'onclick\s*=\s*["\']window\.open',
]

STRIP_SELECTORS = [
    "script[src*='popunder']",
    "script[src*='adsbygoogle']",
    "script[src*='ad.']",
    "iframe[src*='mayzaent']",
    "iframe[src*='ruddy-pass']",
    "iframe[src*='go.godkc']",
    "iframe[src*='cloudflare']",
    "div.bl_layer",
    "div.div_pop",
    "#pop",
]


def is_ad_url(url):
    """Check if a URL looks like an ad."""
    if not url:
        return False
    url_lower = url.lower()
    for domain in AD_DOMAINS:
        if domain in url_lower:
            return True
    for pat in AD_SCRIPT_PATTERNS:
        if re.search(pat, url_lower):
            return True
    return False


def strip_ads_from_html(html_content, page_url=""):
    """Remove ads, popups, and tracking from HTML content."""
    # Remove ad-related script tags
    html_content = re.sub(
        r'<script[^>]*src=["\'][^"\']*(?:popunder|adsbygoogle|ad\.|propellerads|exoclick|pemsrv|tsyndicate|ad-maven|juicyads|trafficjunky|cloudflareinsights|yandex\.ru|mc\.yandex)[^"\']*["\'][^>]*>.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove inline ad scripts (var ad_idzone, ad_popup, etc.)
    html_content = re.sub(
        r'<script[^>]*>\s*var\s+ad_(?:idzone|popup|frequency|trigger|chrome|new_tab|venor)\s*=.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove popup/overlay divs
    html_content = re.sub(
        r'<div[^>]*id=["\']pop["\'][^>]*>.*?</div>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )
    html_content = re.sub(
        r'<div[^>]*class=["\']div_pop["\'][^>]*>.*?</div>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )
    html_content = re.sub(
        r'<div[^>]*class=["\']bl_layer["\'][^>]*>.*?</div>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove ad iframes
    html_content = re.sub(
        r'<iframe[^>]*(?:mayzaent|ruddy-pass|go\.godkc|cloudflare)[^>]*>.*?</iframe>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove onclick popup handlers
    html_content = re.sub(
        r'\s*onclick\s*=\s*["\'][^"\']*window\.open[^"\']*["\']',
        '', html_content, flags=re.IGNORECASE
    )

    # Remove the SCSSpotScript ad loader
    html_content = re.sub(
        r'<script[^>]*id=["\']SCSpotScript["\'][^>]*>.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove ad-related inline scripts (custom_ads, pop1, pop2, etc.)
    html_content = re.sub(
        r'<script[^>]*>\s*(?:var\s+(?:custom_ads|pop\d|popGG|popArai|popunder)\b.*?|document\.getElementById\([\'"]pop[\'"]\).*?)(?=</script>)',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove WordPress popular posts tracking
    html_content = re.sub(
        r'<script[^>]*data-api-url=["\'][^"\']*wordpress-popular-posts[^"\']*["\'][^>]*>.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove googletagmanager/gtag scripts
    html_content = re.sub(
        r'<script[^>]*(?:googletagmanager|gtag|dataLayer)[^>]*>.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove Cloudflare challenge scripts
    html_content = re.sub(
        r'<script[^>]*>.*?__\$cf\$cv\$params.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove Cloudflare beacon
    html_content = re.sub(
        r'<script[^>]*cloudflareinsights\.com[^>]*>.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove Yandex Metrika
    html_content = re.sub(
        r'<script[^>]*mc\.yandex\.ru[^>]*>.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )
    html_content = re.sub(
        r'<noscript>\s*<div[^>]*><img[^>]*mc\.yandex\.ru[^>]*>.*?</div>\s*</noscript>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove W3TC performance tracking
    html_content = re.sub(
        r'Performance optimized by W3 Total Cache.*?(?=</body>|$)',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    # Remove CloudFlare beacon script at end
    html_content = re.sub(
        r'<script[^>]*beacon\.min\.js[^>]*>.*?</script>',
        '', html_content, flags=re.DOTALL | re.IGNORECASE
    )

    return html_content


def inject_parse_button(html_content, page_url):
    """Inject a 'Parse Video Streams' button into video pages."""
    # Only inject on pages that have stream buttons
    if 'wp-btn-iframe' not in html_content and 'STREAM' not in html_content:
        return html_content

    # Extract the title from the page
    title_match = re.search(r'<title>([^<]+)</title>', html_content)
    title = title_match.group(1) if title_match else "Video"

    button_html = f'''
  <style>
  #javproxy-tools {{
      max-height: calc(100vh - 20px);
      overflow-y: auto;
      overscroll-behavior: contain;
      touch-action: pan-y;
      -webkit-overflow-scrolling: touch;
  }}
  #javproxy-tools button {{ touch-action: manipulation; }}
  @media (max-width: 600px) {{
      #javproxy-tools {{
          left: 10px; right: 10px; width: auto; min-width: 0;
          padding: 10px !important; font-size: 12px !important;
      }}
      #javproxy-tools h3 {{ font-size: 13px !important; margin: 0 0 6px 0 !important; }}
      #javproxy-tools #parse-btn {{
          padding: 8px !important; font-size: 12px !important; margin-bottom: 6px !important;
      }}
      #javproxy-tools .host-row {{
          padding: 6px 8px !important; gap: 6px !important;
      }}
      #javproxy-tools .host-row span {{ font-size: 12px !important; }}
      #javproxy-tools .host-row button {{
          padding: 6px 10px !important; font-size: 11px !important;
      }}
      #javproxy-tools .format-row {{
          padding: 4px 0 !important; gap: 6px !important;
      }}
      #javproxy-tools .format-row .fmt-info span {{ font-size: 11px !important; }}
      #javproxy-tools .format-row button {{
          padding: 6px 10px !important; font-size: 11px !important;
      }}
  }}
  </style>
  <div id="javproxy-tools" style="
     position: fixed; top: 10px; right: 10px; z-index: 999999;
     background: #1a1a2e; border: 2px solid #e94560; border-radius: 12px;
     padding: 15px; color: #fff; font-family: Arial, sans-serif;
     box-shadow: 0 8px 32px rgba(0,0,0,0.5); min-width: 320px;
     touch-action: pan-y;
  ">
    <h3 style="margin: 0 0 10px 0; color: #e94560; font-size: 16px;">
        JavProxy Stream Tools
    </h3>
     <button id="parse-btn" onclick="parseStreams()" style="
        width: 100%; padding: 12px; background: #e94560; color: #fff;
        border: none; border-radius: 8px; font-size: 14px; font-weight: bold;
        cursor: pointer; margin-bottom: 10px;
    ">Show Stream Hosts</button>
    <div id="parse-status" style="font-size: 12px; color: #aaa; display: none;"></div>
    <div id="stream-results" style="margin-top: 10px;"></div>
    <div id="format-results" style="margin-top: 10px;"></div>
</div>

<script>
function esc(s) {{
    return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}}

// Keep touch scrolling inside the panel: when the panel hits its top/bottom
// edge, cancel the gesture so the page underneath doesn't scroll. Needed on
// mobile browsers that ignore overscroll-behavior.
(function() {{
    const panel = document.getElementById('javproxy-tools');
    let lastY = null;
    panel.addEventListener('touchstart', function(e) {{
        lastY = e.touches[0].clientY;
    }}, {{ passive: true }});
    panel.addEventListener('touchmove', function(e) {{
        const y = e.touches[0].clientY;
        const dy = lastY - y;
        lastY = y;
        const atTop = panel.scrollTop <= 0;
        const atBottom = panel.scrollTop + panel.clientHeight >= panel.scrollHeight - 1;
        if ((atTop && dy > 0) || (atBottom && dy < 0)) {{
            e.preventDefault();
        }}
    }}, {{ passive: false }});
}})();

function hostRow(label) {{
    return '<div class="host-row" style="display: flex; justify-content: space-between; align-items: center; gap: 10px; padding: 10px; background: #16213e; border: 1px solid #0f3460; border-radius: 8px; margin-bottom: 8px;">'
        + '<span style="color: #fff; font-weight: bold; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;">' + esc(label) + '</span>'
        + '<button onclick="parseHost(this)" data-label="' + esc(label) + '" style="flex: 0 0 auto; padding: 10px 16px; background: #0f3460; color: #fff; border: 1px solid #e94560; border-radius: 6px; cursor: pointer; font-size: 13px;">Parse</button>'
        + '</div>';
}}

function formatRow(fmt, provider) {{
    return '<div class="format-row" style="display: flex; justify-content: space-between; align-items: center; gap: 10px; padding: 8px 0; border-bottom: 1px solid #0f3460;">'
        + '<div class="fmt-info" style="min-width: 0; overflow: hidden; text-overflow: ellipsis;">'
        + '<span style="color: #fff;">' + esc(fmt.resolution) + '</span> '
        + '<span style="color: #888; font-size: 11px;">(' + esc(fmt.codec) + ')</span><br>'
        + '<span style="color: #888; font-size: 11px;">Duration: ' + esc(fmt.duration) + '</span><br>'
        + '<span style="color: #888; font-size: 11px;">Est. size: ' + esc(fmt.size) + '</span>'
        + '</div>'
        + '<button onclick="downloadStream(this)" data-url="' + encodeURIComponent(fmt.url) + '" data-title="' + encodeURIComponent(fmt.title || '') + '" data-provider="' + encodeURIComponent(provider) + '" data-res="' + encodeURIComponent(fmt.resolution || '') + '" data-referer="' + encodeURIComponent(fmt._referer || '') + '" style="'
        + 'flex: 0 0 auto; padding: 10px 16px; background: #0f3460; color: #fff; border: 1px solid #e94560;'
        + 'border-radius: 6px; cursor: pointer; font-size: 13px; white-space: nowrap;'
        + '">Download</button>'
        + '</div>';
}}

async function parseStreams() {{
    const btn = document.getElementById('parse-btn');
    const status = document.getElementById('parse-status');
    const results = document.getElementById('stream-results');
    const fmts = document.getElementById('format-results');

    btn.disabled = true;
    btn.textContent = 'Loading hosts...';
    status.style.display = 'block';
    status.textContent = 'Fetching available hosts...';
    results.innerHTML = '';
    fmts.innerHTML = '';

    try {{
        const resp = await fetch('/api/hosts?url=' + encodeURIComponent(window.location.href));
        const data = await resp.json();

        if (data.error) {{
            throw new Error(data.error);
        }}
        if (!data.hosts.length) {{
            throw new Error('No parseable hosts found on this page');
        }}

        results.innerHTML = data.hosts.map(h => hostRow(h.label)).join('');
        status.textContent = data.hosts.length + ' host(s) available — pick one to parse.';
    }} catch (e) {{
        status.innerHTML = '<span style="color: #ff6b6b;">Error: ' + esc(e.message) + '</span>';
    }}

    btn.disabled = false;
    btn.textContent = 'Show Stream Hosts';
}}

async function parseHost(btn) {{
    const label = btn.dataset.label;
    const status = document.getElementById('parse-status');
    const fmts = document.getElementById('format-results');

    btn.disabled = true;
    btn.textContent = 'Parsing...';
    status.style.display = 'block';
    status.textContent = 'Parsing ' + label + '...';
    fmts.innerHTML = '';

    try {{
        const resp = await fetch('/api/parse?url=' + encodeURIComponent(window.location.href) + '&provider=' + encodeURIComponent(label));
        const data = await resp.json();

        if (data.error) {{
            throw new Error(data.error);
        }}
        const stream = data.streams[0];
        if (stream.error) {{
            throw new Error(stream.error);
        }}

        status.textContent = 'Found ' + stream.formats.length + ' format(s) on ' + label + '.';
        let html = '<div style="background: #16213e; border-radius: 8px; padding: 12px; border: 1px solid #0f3460;">';
        html += '<div style="font-weight: bold; color: #e94560; margin-bottom: 6px;">' + esc(stream.provider) + '</div>';
        for (const fmt of stream.formats) {{
            html += formatRow(fmt, stream.provider);
        }}
        html += '</div>';
        fmts.innerHTML = html;
    }} catch (e) {{
        fmts.innerHTML = '<div style="color: #ff6b6b; font-size: 12px;">' + esc(e.message) + '</div>';
    }}

    btn.disabled = false;
    btn.textContent = 'Parse';
}}

async function downloadStream(btn) {{
    const url = decodeURIComponent(btn.dataset.url);
    const title = decodeURIComponent(btn.dataset.title || 'video');
    btn.disabled = true;
    btn.textContent = 'Starting...';

    try {{
        const resp = await fetch('/api/download', {{
            method: 'POST',
            headers: {{'Content-Type': 'application/json'}},
            body: JSON.stringify({{
                url: url,
                title: title,
                page_url: window.location.href,
                provider: decodeURIComponent(btn.dataset.provider || ''),
                resolution: decodeURIComponent(btn.dataset.res || ''),
                referer: decodeURIComponent(btn.dataset.referer || '')
            }})
        }});
        const data = await resp.json();
        if (data.error) {{
            btn.textContent = 'Error: ' + data.error;
            btn.disabled = false;
            return;
        }}
        btn.textContent = 'Queued #' + data.id + ' — see Downloads';
        pollDownload(data.id, btn);
    }} catch (e) {{
        btn.textContent = 'Error: ' + e.message;
        btn.disabled = false;
    }}
}}

function pollDownload(id, btn) {{
    const interval = setInterval(async () => {{
        try {{
            const resp = await fetch('/api/download/' + id);
            const data = await resp.json();

            if (data.status === 'downloading') {{
                btn.textContent = data.progress || 'Downloading...';
                // Show a cancel button next to the download button
                if (!btn.nextElementSibling || !btn.nextElementSibling.classList.contains('cancel-btn')) {{
                    const cancel = document.createElement('button');
                    cancel.className = 'cancel-btn';
                    cancel.textContent = 'Cancel';
                    cancel.style.cssText = 'margin-left: 6px; padding: 10px 14px; background: #6b2121; color: #fff; border: 1px solid #ff6b6b; border-radius: 6px; cursor: pointer; font-size: 12px; touch-action: manipulation;';
                    cancel.onclick = function() {{ cancelDownload(id, btn, cancel); }};
                    btn.parentNode.insertBefore(cancel, btn.nextSibling);
                }}
            }} else if (data.status === 'done') {{
                clearInterval(interval);
                // Remove cancel button if present
                const cancelBtn = btn.nextElementSibling;
                if (cancelBtn && cancelBtn.classList.contains('cancel-btn')) cancelBtn.remove();
                btn.textContent = 'Save As...';
                btn.disabled = false;
                btn.onclick = function() {{
                    window.location.href = '/api/file/' + id;
                }};
            }} else if (data.status === 'error' || data.status === 'cancelled') {{
                clearInterval(interval);
                const cancelBtn = btn.nextElementSibling;
                if (cancelBtn && cancelBtn.classList.contains('cancel-btn')) cancelBtn.remove();
                btn.textContent = data.status === 'cancelled' ? 'Cancelled' : 'Error: ' + (data.error || 'unknown');
                btn.disabled = false;
            }} else if (data.status === 'interrupted') {{
                clearInterval(interval);
                const cancelBtn = btn.nextElementSibling;
                if (cancelBtn && cancelBtn.classList.contains('cancel-btn')) cancelBtn.remove();
                btn.textContent = 'Interrupted — resume in Downloads';
                btn.disabled = false;
                btn.onclick = function() {{ window.location.href = '/downloads'; }};
            }}
        }} catch (e) {{
            // keep polling
        }}
    }}, 1000);
}}

async function cancelDownload(id, btn, cancelBtn) {{
    cancelBtn.textContent = 'Cancelling...';
    cancelBtn.disabled = true;
    try {{
        await fetch('/api/download/' + id, {{ method: 'DELETE' }});
        cancelBtn.textContent = 'Cancelled';
    }} catch (e) {{
        cancelBtn.textContent = 'Error';
        cancelBtn.disabled = false;
    }}
}}
</script>
'''
    # Insert before </body>
    html_content = html_content.replace('</body>', button_html + '\n</body>')
    return html_content


def rewrite_urls(html_content, proxy_prefix):
    """Rewrite absolute URLs to go through the proxy.

    Preserves the original quote character (single or double) so that HTML
    attributes like  href='...'  don't end up with mismatched quotes.
    """
    html_content = re.sub(
        r"""(href|src|action)=(['"])https?://jav\.guru""",
        lambda m: f'{m.group(1)}={m.group(2)}{proxy_prefix}',
        html_content
    )
    html_content = re.sub(
        r"""(href|src|action)=(['"])https?://cdn\.javmiku\.com""",
        lambda m: f'{m.group(1)}={m.group(2)}{proxy_prefix}/cdn/javmiku',
        html_content
    )
    html_content = re.sub(
        r"""(href|src|action)=(['"])https?://cdn\.javnorth\.com""",
        lambda m: f'{m.group(1)}={m.group(2)}{proxy_prefix}/cdn/javnorth',
        html_content
    )
    return html_content


# ── Stream extraction ───────────────────────────────────────────────────────

def fetch_url(url, referer=None, timeout=10):
    """Fetch a URL and return the response body as string."""
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.5",
    }
    if referer:
        headers["Referer"] = referer
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = resp.read()
            # Try UTF-8, fallback to latin-1
            try:
                return data.decode("utf-8")
            except UnicodeDecodeError:
                return data.decode("latin-1")
    except Exception as e:
        return None


def fetch_url_bytes(url, referer=None, timeout=10):
    """Fetch a URL and return the raw bytes + Content-Type.

    Used by the CDN proxy to serve binary assets (images, fonts) without
    corrupting them through text decoding."""
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
        "Accept": "*/*",
        "Accept-Language": "en-US,en;q=0.5",
        "Referer": referer or BASE_URL,
    }
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read(), resp.headers.get("Content-Type", "application/octet-stream")
    except Exception:
        return None, None


def fetch_url_full(url, referer=None, timeout=20):
    """Fetch a URL, follow redirects, and return (body, final_url).

    The final_url is the real provider origin after the jav.guru 302, which is
    what relative stream URLs (e.g. /pass_md5/, /stream/*.m3u8) resolve against.
    Returns (None, url) on failure.
    """
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.5",
    }
    if referer:
        headers["Referer"] = referer
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = resp.read()
            try:
                body = data.decode("utf-8")
            except UnicodeDecodeError:
                body = data.decode("latin-1")
            return body, resp.geturl()
    except Exception:
        return None, url


def extract_base64_iframe_urls(page_html):
    """Extract base64-encoded iframe URLs from wp-btn-iframe data."""
    streams = []

    # Pattern: var VARIABENAME = {..., "iframe_url":"BASE64..."...};
    pattern = r'var\s+(\w+)\s*=\s*\{[^}]*"iframe_url"\s*:\s*"([A-Za-z0-9+/=]+)"[^}]*\}'
    matches = re.findall(pattern, page_html)

    # Also look for the button labels
    btn_pattern = r'<a[^>]*data-localize="(\w+)"[^>]*>([^<]+)</a>'
    btn_matches = re.findall(btn_pattern, page_html)
    btn_map = {m[0]: m[1].strip() for m in btn_matches}

    for var_name, b64_url in matches:
        try:
            decoded = base64.b64decode(b64_url).decode("utf-8")
            label = btn_map.get(var_name, var_name)
            streams.append({"label": label, "url": decoded, "var": var_name})
        except Exception:
            pass

    return streams


def decode_intermediate_page(page_html):
    """From the intermediate /searcho/ page, extract the token and build the player URL."""
    # Find the data attributes: data-XXXXX="value"
    data_attrs = re.findall(r'data-(\w+)="([0-9a-f]+)"', page_html)
    # Find the rtype and base
    cfg_match = re.search(
        r'window\.cfg\s*=\s*\{[^}]*base\s*:\s*[\'"]([^\'"]+)[\'"][^}]*rtype\s*:\s*[\'"](\w)[\'"]',
        page_html, re.DOTALL
    )
    if not cfg_match or len(data_attrs) < 3:
        return None

    base = cfg_match.group(1)
    rtype = cfg_match.group(2)

    # Concatenate the three data attribute values and reverse
    full_token = "".join(v for _, v in data_attrs[:3])
    reversed_token = full_token[::-1]

    return f"{base}?{rtype}r={reversed_token}"


# ── Per-provider stream extractors ──────────────────────────────────────────
#
# Provider is detected from the player page's domain. Each returns a dict:
#   {"url": <stream url>, "kind": "m3u8"|"mp4", "referer": <str|None>}
# or None if the URL could not be found.

def _to_base36(n, b):
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"
    s = ""
    while n:
        n, r = divmod(n, b)
        s = digits[r] + s
    return s or "0"


def _parse_js_qstring(html, pos):
    """Parse a single-quoted JS string literal starting at html[pos]=="'".

    Returns (content_with_escapes, position_after_closing_quote).
    """
    assert html[pos] == "'"
    pos += 1
    out = []
    while pos < len(html):
        ch = html[pos]
        if ch == "\\":
            out.append(html[pos:pos + 2])
            pos += 2
            continue
        if ch == "'":
            return "".join(out), pos + 1
        out.append(ch)
        pos += 1
    raise ValueError("unterminated JS string")


def decode_base36_eval(page_html):
    """Decode the `eval(function(p,a,c,k,e,d){...}('code',a,c,'dict'))` obfuscation
    used by the SB / DD / EXTRA players. Returns the de-obfuscated JS, or None."""
    i = page_html.find("eval(function")
    if i < 0:
        return None
    start = page_html.find("}('", i)
    if start < 0:
        return None
    try:
        code, pos = _parse_js_qstring(page_html, start + 2)
        rest = page_html[pos:]
        m = re.match(r"\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*", rest)
        if not m:
            return None
        a = int(m.group(1))
        c = int(m.group(2))
        dpos = pos + m.end()
        if page_html[dpos] != "'":
            return None
        dstr, _ = _parse_js_qstring(page_html, dpos)
    except (AssertionError, ValueError, IndexError):
        return None

    karr = dstr.split("|")
    p = code.encode().decode("unicode_escape")
    for idx in range(c - 1, -1, -1):
        if idx < len(karr) and karr[idx]:
            p = re.sub(
                r"\b" + re.escape(_to_base36(idx, a)) + r"\b",
                lambda mm, k=karr[idx]: k.replace("\\", "\\\\"),
                p,
            )
    return p


def _resolve(base_url, url):
    """Resolve a possibly-relative stream URL against the player origin."""
    if not url:
        return None
    if url.startswith("http://") or url.startswith("https://"):
        return url
    if url.startswith("//"):
        return "https:" + url
    return urllib.parse.urljoin(base_url, url)


def extract_tv(player_html, player_url):
    """TV (turboviplay.com): plain `var urlPlay='...m3u8'`."""
    m = re.search(r"var\s+urlPlay\s*=\s*['\"]([^'\"]+)['\"]", player_html)
    if m:
        return {"url": _resolve(player_url, m.group(1)), "kind": "m3u8"}
    m = re.search(r'data-hash="([^"]+\.m3u8[^"]*)"', player_html)
    if m:
        return {"url": _resolve(player_url, m.group(1)), "kind": "m3u8"}
    m = re.search(r'https?://[^\s"\'<>]+\.m3u8[^\s"\'<>]*', player_html)
    if m:
        return {"url": m.group(0), "kind": "m3u8"}
    return None


def _extract_links_hls(js, player_url):
    """From SB's decoded `var links={hls2/hls3/hls4}` collect all m3u8 qualities.

    Returns a list of {"url","kind","label"} ordered best-first, or None."""
    m = re.search(r'var\s+links\s*=\s*(\{[^}]*\})', js)
    if not m:
        return None
    obj = m.group(1)
    out = []
    seen = set()
    for key in ("hls2", "hls3", "hls4", "hls"):
        km = re.search(r'"%s"\s*:\s*"([^"]+\.m3u8[^"]*)"' % re.escape(key), obj)
        if km:
            url = _resolve(player_url, km.group(1))
            if url not in seen:
                seen.add(url)
                out.append({"url": url, "kind": "m3u8", "label": key})
    if out:
        return out
    # Fallback: any .m3u8 values in the object
    for km in re.finditer(r'"[^"]+"\s*:\s*"((?:https?://|/)[^"]+\.m3u8[^"]*)"', obj):
        url = _resolve(player_url, km.group(1))
        if url not in seen:
            seen.add(url)
            out.append({"url": url, "kind": "m3u8", "label": "hls"})
    return out or None


def _extract_links_hls_from_js(js, player_url):
    """SB (javclan.com / StreamHG): decoded `var links={hls2/hls4}` -> m3u8."""
    return _extract_links_hls(js, player_url)


def _extract_jwplayer_file(js, player_url):
    """LU (streamhihi.com / LuluStream): JWPlayer `sources:[{file}]`."""
    m = re.search(r'sources\s*:\s*\[\s*\{[^}]*?file\s*:\s*"(https?://[^"]+)"', js)
    if m:
        url = m.group(1)
        kind = "m3u8" if ".m3u8" in url else "mp4"
        return {"url": url, "kind": kind}
    m = re.search(r'sources\s*:\s*\[\s*\{[^}]*?file\s*:\s*"([^"]+)"', js)
    if m:
        url = _resolve(player_url, m.group(1))
        kind = "m3u8" if ".m3u8" in url else "mp4"
        return {"url": url, "kind": kind}
    m = re.search(r'file\s*:\s*"(https?://[^"]+\.m3u8[^"]*)"', js)
    if m:
        return {"url": m.group(1), "kind": "m3u8"}
    return None


def _extract_playerjs_file(js, player_url):
    """EXTRA (maxstream.org): Playerjs `file:"...m3u8"` -> m3u8."""
    m = re.search(r'file\s*:\s*"(https?://[^"]+\.m3u8[^"]*)"', js)
    if m:
        return {"url": m.group(1), "kind": "m3u8"}
    m = re.search(r'file\s*:\s*"([^"]+\.m3u8[^"]*)"', js)
    if m:
        return {"url": _resolve(player_url, m.group(1)), "kind": "m3u8"}
    return None


_JUICY_SYMBOLS = ["`", "%", "-", "+", "*", "$", "!", "_", "^", "="]


def _juicy_decode(encoded):
    """Decode the `_juicycodes(...)` obfuscation used by AV (oppainet.net).

    The payload is a base64 body followed by three salt characters. The salt
    is the concatenation of (charCode - 100) for those three chars. The base64
    body decodes to a string of `_JUICY_SYMBOLS` characters, each mapping to a
    digit 0-9; every group of four digits is (value % 1000) - salt, i.e. one
    character of the de-obfuscated JS.
    """
    salt = int("".join(str(ord(c) - 100) for c in encoded[-3:]))
    body = encoded[:-3].replace("_", "+").replace("-", "/")
    body += "=" * ((4 - len(body) % 4) % 4)
    stage = base64.b64decode(body).decode("latin-1")
    digits = "".join(str(_JUICY_SYMBOLS.index(c)) for c in stage)
    groups = re.findall(r".{4}", digits)
    return "".join(chr((int(g) % 1000) - salt) for g in groups)


def _extract_balanced_object(text, key):
    """Return the balanced `{...}` JSON object assigned via `key =`."""
    m = re.search(re.escape(key) + r"\s*=\s*\{", text)
    if not m:
        return None
    start = text.index("{", m.start())
    depth = 0
    in_str = False
    esc = False
    for i in range(start, len(text)):
        ch = text[i]
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
    return None


def extract_av(player_html, player_url):
    """AV (oppainet.net): de-obfuscate the `_juicycodes` JWPlayer config.

    The embed hides its JWPlayer setup inside `_juicycodes("...")`; decoding it
    yields `var config = {...}` whose `sources.file` is the HLS master URL."""
    m = re.search(r"_juicycodes\((.*?)\);", player_html, re.S)
    if not m:
        return None
    try:
        parts = re.findall(r'"((?:[^"\\]|\\.)*)"', m.group(1))
        encoded = "".join(json.loads('"' + p + '"') for p in parts)
        js = _juicy_decode(encoded)
    except (ValueError, KeyError, IndexError):
        return None
    obj = _extract_balanced_object(js, "config")
    if not obj:
        return None
    try:
        cfg = json.loads(obj)
    except json.JSONDecodeError:
        return None
    src = cfg.get("sources")
    if isinstance(src, dict):
        url = src.get("file")
    elif isinstance(src, list) and src:
        url = src[0].get("file")
    else:
        url = None
    if not url:
        return None
    return {"url": url, "kind": "m3u8"}


def extract_jk(player_html, player_url):
    """JK (playmogo.com / vide0.net / DoodStream): GET /pass_md5/{hash}/{token}.

    The endpoint returns a base URL; append a random 10-char suffix plus
    ?token=<token>&expiry=<now ms> to get the progressive MP4."""
    m = re.search(r'/pass_md5/([0-9a-fA-F\-]+)/([A-Za-z0-9]+)', player_html)
    if not m:
        return None
    path, token = m.group(1), m.group(2)
    origin = urllib.parse.urlparse(player_url).scheme + "://" + urllib.parse.urlparse(player_url).netloc
    base = fetch_url(f"{origin}/pass_md5/{path}/{token}", referer=player_url)
    if not base:
        return None
    base = base.strip().splitlines()[0].strip()
    if not base.startswith("http"):
        return None
    suffix = "".join(random.choices(string.ascii_letters + string.digits, k=10))
    expiry = str(int(time.time() * 1000))
    return {"url": f"{base}{suffix}?token={token}&expiry={expiry}", "kind": "mp4"}


def extract_vo(player_html, player_url):
    """VO (jamesbornmain.com / voe.sx).

    The real stream URL is assembled by the external jwplayer.js (payload +
    cookie + token), so the inline-script Node sandbox (vo_decode.js) cannot
    reach it. A headless browser is required. Until that is added, VO is
    reported as unsupported.
    """
    return None


def _extract_vo_via_node(player_html, player_url):
    """[disabled] Node vm-sandbox VO decoder. Kept for a future headless-browser
    fallback; returns the decoded CDN URLs (ads) only, not the video."""
    if not shutil.which("node"):
        return None
    try:
        proc = subprocess.run(
            ["node", os.path.join(os.path.dirname(os.path.abspath(__file__)), "vo_decode.js"), "-", player_url],
            input=player_html,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=45, text=True,
        )
        if proc.returncode != 0:
            return None
        data = json.loads(proc.stdout)
        url = data.get("file")
        if not url:
            return None
        kind = "m3u8" if ".m3u8" in url else "mp4"
        return {"url": url, "kind": kind, "title": data.get("title"),
                "all_urls": data.get("urls", [])}
    except Exception:
        return None


def extract_stream_url(player_html, player_url):
    """Extract stream URLs, detecting the provider from page CONTENT.

    Returns a list of {"url","kind"} ordered best-first (may be empty).
    jav.guru embeds every provider's player inline (the player_url is always a
    jav.guru embed that 302s to the provider), so the provider is identified by
    the page content, not the URL. `player_url` must be the post-redirect
    provider origin so relative stream URLs resolve correctly.
    """
    # 1. TV (turboviplay): plain `var urlPlay='...m3u8'`.
    got = extract_tv(player_html, player_url)
    if got:
        return [got]

    # 2. JK (DoodStream / playmogo / vide0): /pass_md5/{hash}/{token} -> MP4.
    if "pass_md5" in player_html:
        got = extract_jk(player_html, player_url)
        if got:
            return [got]

    # 3. AV (oppainet.net): de-obfuscate the `_juicycodes` JWPlayer config.
    if "_juicycodes(" in player_html:
        got = extract_av(player_html, player_url)
        if got:
            return [got]

    # 4. Base-36 `eval(...)` players (SB / DD / EXTRA): decode once, inspect.
    js = decode_base36_eval(player_html)
    if js:
        got = _extract_links_hls_from_js(js, player_url)   # SB (multi-quality)
        if got:
            return got
        got = _extract_jwplayer_file(js, player_url)       # LU (LuluStream)
        if got:
            return [got]
        got = _extract_playerjs_file(js, player_url)       # EXTRA
        if got:
            return [got]

    return []


def parse_hls_master(master_url, referer=None):
    """If master_url is a master playlist, return its variants (best-first).

    Each variant: {"url","resolution","bandwidth","codecs"}.
    Returns None if the URL is not a master playlist (i.e. a media playlist).
    """
    content = fetch_url(master_url, referer=referer)
    if not content or "#EXT-X-STREAM-INF" not in content:
        return None
    lines = [l.strip() for l in content.splitlines()]
    variants = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("#EXT-X-STREAM-INF"):
            attrs = line.split(":", 1)[1] if ":" in line else ""
            res_m = re.search(r"RESOLUTION=(\d+x\d+)", attrs)
            bw_m = re.search(r"BANDWIDTH=(\d+)", attrs)
            codecs_m = re.search(r'CODECS="([^"]+)"', attrs)
            j = i + 1
            while j < len(lines) and (not lines[j] or lines[j].startswith("#")):
                j += 1
            if j < len(lines):
                vurl = lines[j]
                if not vurl.startswith("http"):
                    vurl = urllib.parse.urljoin(master_url, vurl)
                variants.append({
                    "url": vurl,
                    "resolution": res_m.group(1) if res_m else "Unknown",
                    "bandwidth": int(bw_m.group(1)) if bw_m else 0,
                    "codecs": codecs_m.group(1) if codecs_m else "Unknown",
                })
                i = j
        i += 1
    variants.sort(key=lambda v: (v["bandwidth"], v["resolution"]), reverse=True)
    return variants or None


def playlist_duration(url):
    """Fetch a media playlist and return (total_seconds, segment_count)."""
    content = fetch_url(url)
    if not content:
        return 0, 0
    durations = [float(m) for m in re.findall(r'#EXTINF:([\d.]+)', content)]
    return sum(durations), len(durations)


def get_stream_info(m3u8_url):
    """Fetch m3u8 and extract resolution, duration, segment count."""
    content = fetch_url(m3u8_url)
    if not content:
        return {"error": "Failed to fetch m3u8"}

    info = {
        "url": m3u8_url,
        "resolution": "Unknown",
        "codec": "Unknown",
        "duration": "Unknown",
        "total_seconds": 0,
        "segments": 0,
        "encrypted": False,
        "size": "Unknown",
    }

    # Check if it's a master playlist
    stream_match = re.search(r'#EXT-X-STREAM-INF:BANDWIDTH=(\d+),RESOLUTION=(\d+x\d+),CODECS="([^"]+)"', content)
    if stream_match:
        info["bandwidth"] = int(stream_match.group(1))
        info["resolution"] = stream_match.group(2)
        info["codec"] = stream_match.group(3)
        # Follow the nested playlist
        lines = content.strip().split("\n")
        for i, line in enumerate(lines):
            if line.strip() and not line.startswith("#") and i > 0:
                nested_url = line.strip()
                if not nested_url.startswith("http"):
                    nested_url = urllib.parse.urljoin(m3u8_url, nested_url)
                nested_content = fetch_url(nested_url)
                if nested_content:
                    content = nested_content
                    m3u8_url = nested_url
                break

    # Parse segment durations
    durations = [float(m) for m in re.findall(r'#EXTINF:([\d.]+)', content)]
    if durations:
        total = sum(durations)
        info["segments"] = len(durations)
        info["total_seconds"] = total
        hours = int(total // 3600)
        mins = int((total % 3600) // 60)
        secs = int(total % 60)
        info["duration"] = f"{hours}h {mins}m {secs}s"

    # Check encryption
    if '#EXT-X-KEY' in content:
        info["encrypted"] = True

    # Estimate file size from bandwidth
    if "bandwidth" in info and info["total_seconds"] > 0:
        bytes_est = info["bandwidth"] * info["total_seconds"] / 8
        if bytes_est > 1048576:
            info["size"] = f"~{bytes_est / 1048576:.1f} MB"
        else:
            info["size"] = f"~{bytes_est / 1024:.1f} KB"

    # Try to get more accurate size by checking a few segment file sizes
    seg_urls = re.findall(r'https?://[^\s"\'<>]+(?=\s|$)', content)
    seg_urls = [u for u in seg_urls if not u.startswith("http") or ".m3u8" not in u]
    seg_urls = [u for u in seg_urls if "tiktokcdn" in u or "turboviplay" in u or "turbosplayer" in u]

    if seg_urls and info["total_seconds"] > 0:
        # Sample a few segments
        total_sample_size = 0
        sampled = 0
        for seg_url in seg_urls[:3]:
            try:
                req = urllib.request.Request(seg_url, method="HEAD", headers={
                    "User-Agent": "Mozilla/5.0",
                })
                with urllib.request.urlopen(req, timeout=10) as resp:
                    size = resp.headers.get("Content-Length")
                    if size:
                        total_sample_size += int(size)
                        sampled += 1
            except Exception:
                pass

        if sampled > 0:
            avg_seg_size = total_sample_size / sampled
            avg_seg_duration = sum(durations[:sampled]) / sampled if durations else 5
            total_bytes = avg_seg_size * info["total_seconds"] / avg_seg_duration
            if total_bytes > 1048576:
                info["size"] = f"~{total_bytes / 1048576:.0f} MB (actual)"
            info["avg_segment_bytes"] = int(avg_seg_size)

    return info


def get_mp4_info(mp4_url, referer=None):
    """HEAD a progressive MP4 (DoodStream/JK) and report size + content type."""
    info = {
        "url": mp4_url,
        "resolution": "Unknown",
        "codec": "mp4",
        "duration": "Unknown",
        "total_seconds": 0,
        "segments": 0,
        "encrypted": False,
        "size": "Unknown",
    }
    try:
        req = urllib.request.Request(mp4_url, method="HEAD", headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",
            **({"Referer": referer} if referer else {}),
        })
        with urllib.request.urlopen(req, timeout=15) as resp:
            length = resp.headers.get("Content-Length")
            ctype = resp.headers.get("Content-Type", "")
            if length:
                b = int(length)
                info["size"] = f"~{b / 1048576:.0f} MB"
            info["codec"] = ctype.split(";")[0].strip() or "mp4"
            # Providers sometimes return a thumbnail/error image instead of
            # video (expired token, blocked IP). Reject before downloading.
            if ctype.startswith("image/") or ctype.startswith("text/"):
                info["error"] = f"Stream URL returned {ctype}, not video (URL may be expired)"
    except Exception as e:
        info["error"] = str(e)
    return info


# Hosts we cannot decode yet. VO (jamesbornmain.com / voe.sx) assembles its
# stream URL in an external jwplayer.js, so it needs a headless browser (see
# extract_vo). Hidden from the host list until that is added.
UNSUPPORTED_PROVIDERS = {"vo"}


def _provider_code(label):
    """Normalise a host label like 'STREAM VO' to its code ('vo')."""
    code = label.strip().lower()
    if code.startswith("stream "):
        code = code[len("stream "):]
    return code


def list_page_hosts(page_url):
    """Return the hosts on a video page that we can actually parse."""
    page_html = fetch_url(page_url, referer=BASE_URL)
    if not page_html:
        return {"error": "Failed to fetch page"}
    streams = extract_base64_iframe_urls(page_html)
    hosts = [
        {"label": s["label"], "var": s["var"]}
        for s in streams
        if _provider_code(s["label"]) not in UNSUPPORTED_PROVIDERS
    ]
    return {"hosts": hosts}


def extract_streams_from_page(page_url, provider=None):
    """Main extraction pipeline: given a jav.guru video page URL, extract streams.

    If `provider` (a host label) is given, only that host is resolved."""
    page_html = fetch_url(page_url, referer=BASE_URL)
    if not page_html:
        return {"error": "Failed to fetch page"}

    # Get title
    title_match = re.search(r'<title>([^<]+)</title>', page_html)
    title = title_match.group(1).strip() if title_match else "video"
    # Clean title for filename
    title = re.sub(r'[^\w\s\-]', '', title)[:80].strip()

    # Extract base64 iframe URLs
    b64_streams = extract_base64_iframe_urls(page_html)
    if provider is not None:
        b64_streams = [s for s in b64_streams if s["label"].lower() == provider.lower()]
        if not b64_streams:
            return {"error": f"Host '{provider}' not found on this page", "title": title}
    if not b64_streams:
        return {"error": "No stream buttons found on this page", "title": title}

    # Providers are fetched concurrently — total time ~= slowest provider,
    # not the sum, so a single flaky CDN can't stall the whole parse.
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(b64_streams)) as pool:
        results = list(pool.map(
            lambda s: _extract_one_provider(s, page_url, title), b64_streams
        ))

    return {"title": title, "streams": results}


def _extract_one_provider(stream, page_url, title):
    """Resolve a single provider's stream URL + info. Returns a result dict."""
    provider = stream["label"]
    intermediate_url = stream["url"]

    # Fetch intermediate page
    intermediate_html = fetch_url(intermediate_url, referer=page_url)
    if not intermediate_html:
        return {"provider": provider, "error": "Failed to fetch intermediate page"}

    # Decode the token and get player URL
    player_url = decode_intermediate_page(intermediate_html)
    if not player_url:
        return {"provider": provider, "error": "Failed to decode stream token"}

    # Fetch player page, following the 302 to the real provider origin.
    player_html, final_url = fetch_url_full(player_url, referer=intermediate_url)
    if not player_html:
        return {"provider": provider, "error": "Failed to fetch player page"}

    # Extract stream URLs (provider detected from content), best-first.
    got_list = extract_stream_url(player_html, final_url)
    if not got_list:
        if "embed restricted" in player_html.lower():
            return {"provider": provider, "error": "Embed restricted for this domain"}
        return {"provider": provider, "error": "No stream URL found"}

    # Expand each URL into downloadable formats: an m3u8 master playlist
    # yields one format per resolution; everything else is a single format.
    formats = []
    kind = got_list[0].get("kind", "m3u8")
    for got in got_list:
        if got.get("kind") == "m3u8":
            variants = parse_hls_master(got["url"], referer=final_url)
            if variants:
                for v in variants:
                    formats.append({
                        "url": v["url"],
                        "type": "m3u8",
                        "resolution": v["resolution"],
                        "codec": v["codecs"],
                        "_bandwidth": v["bandwidth"],
                        "_referer": final_url,
                    })
            else:
                formats.append({
                    "url": got["url"],
                    "type": "m3u8",
                    "resolution": "Unknown",
                    "codec": "Unknown",
                    "_bandwidth": 0,
                    "_referer": final_url,
                })
        else:
            formats.append({
                "url": got["url"],
                "type": "mp4",
                "resolution": "Unknown",
                "codec": "mp4",
                "_bandwidth": 0,
                "_referer": final_url,
            })

    # Fill in duration / size for every format.
    if kind == "m3u8":
        total, _segs = playlist_duration(formats[0]["url"])
        hours, mins, secs = int(total // 3600), int((total % 3600) // 60), int(total % 60)
        duration = f"{hours}h {mins}m {secs}s" if total else "Unknown"
        for f in formats:
            f["duration"] = duration
            if f["_bandwidth"] and total:
                f["size"] = f"~{f['_bandwidth'] * total / 8 / 1048576:.0f} MB"
            else:
                f["size"] = "Unknown"
    else:
        info = get_mp4_info(formats[0]["url"], referer=final_url)
        if "not video" in info.get("error", ""):
            return {"provider": provider, "error": info["error"]}
        for f in formats:
            f["duration"] = info.get("duration", "Unknown")
            f["size"] = info.get("size", "Unknown")
            if info.get("codec"):
                f["codec"] = info["codec"]

    for f in formats:
        f["title"] = title
        del f["_bandwidth"]

    return {
        "provider": provider,
        "formats": formats,
        "m3u8_url": formats[0]["url"] if kind == "m3u8" else None,
        "stream_url": formats[0]["url"],
        "kind": kind,
    }


# ── Download management ─────────────────────────────────────────────────────

def looks_like_video(path):
    """Check file magic bytes to confirm the download is actually a video.

    Providers occasionally serve an error/thumbnail PNG at the stream URL;
    catching it here prevents a 3GB garbage file from being marked 'done'.
    Note: some CDNs prepend a PNG splash frame *before* the MPEG-TS payload —
    that is recoverable (finalize_video remuxes it), so video markers are
    checked first.
    """
    try:
        with open(path, "rb") as f:
            head = f.read(65536)
    except OSError:
        return False
    if b"ftyp" in head or _find_ts_sync(head) is not None:
        return True  # mp4/mov, or TS payload (possibly behind a PNG prefix)
    if head.startswith(b"OggS") or head.startswith(b"\x1a\x45\xdf\xa3"):
        return True  # ogg / webm
    if head.startswith(b"\x89PNG") or head.startswith(b"GIF8") or head.startswith(b"\xff\xd8\xff"):
        return False  # image with no video data behind it
    if head.lstrip()[:1] in (b"<", b"{") or b"<!DOCTYPE" in head[:1024] or b"<html" in head[:1024].lower():
        return False  # html / json error page
    if head.startswith(b"#EXTM3U"):
        return False  # raw playlist dumped as a file
    # fMP4 segments and some muxers have no magic at offset 0; allow unknown
    # binary content that isn't clearly an image/html/playlist.
    return True


def find_stream_for_resume(page_url, provider, resolution):
    """Re-parse a video page and find the format matching provider+resolution."""
    if not page_url:
        return None
    # page_url is usually the proxy URL (window.location.href); convert it
    # back to the upstream jav.guru URL, same as /api/parse does.
    p = urllib.parse.urlparse(page_url)
    upstream = BASE_URL + p.path + (("?" + p.query) if p.query else "")
    result = extract_streams_from_page(upstream, provider)
    if result.get("error"):
        return None
    for s in result.get("streams", []):
        if s.get("error") or s.get("provider") != provider:
            continue
        formats = s.get("formats", [])
        if not formats:
            continue
        pick = None
        if resolution:
            for f in formats:
                if f.get("resolution") == resolution:
                    pick = f
                    break
        if pick is None:
            pick = formats[0]
        return pick
    return None


def _find_ts_sync(buf):
    """Offset of an MPEG-TS sync (5x consecutive 0x47 at 188-byte spacing), or None."""
    limit = max(0, len(buf) - 188 * 5)
    for start in range(limit):
        if buf[start] == 0x47 and all(buf[start + n * 188] == 0x47 for n in range(1, 5)):
            return start
    return None


def finalize_video(path):
    """Post-process a finished download; returns (ok, message).

    Some CDNs prepend a small PNG splash frame and serve MPEG-TS payloads
    under an .mp4 name. If the file isn't a real MP4 (ftyp box), remux it
    with ffmpeg (stream copy, no re-encode) into a clean MP4 container.
    """
    try:
        with open(path, "rb") as f:
            head = f.read(64)
    except OSError:
        return False, "unreadable"
    if head[4:8] == b"ftyp":
        return True, "ok"

    # Look for recoverable video data (TS sync or ftyp) within the first 64KB.
    with open(path, "rb") as f:
        chunk = f.read(65536)
    ts_sync = _find_ts_sync(chunk)
    if b"ftyp" not in chunk and ts_sync is None:
        return False, "no video data found"

    if not shutil.which("ffmpeg"):
        return False, "ffmpeg not available to remux"

    out = path + ".remux.mp4"
    try:
        # Force the TS demuxer: the leading PNG splash frames otherwise get
        # probed as the video stream and the real TS payload is ignored.
        cmd = ["ffmpeg", "-y", "-fflags", "+discardcorrupt"]
        if ts_sync is not None:
            cmd += ["-f", "mpegts"]
        cmd += ["-i", path, "-c", "copy", "-movflags", "+faststart", "-f", "mp4", out]
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=900,
        )
        if proc.returncode == 0 and os.path.exists(out) and os.path.getsize(out) > 1024 * 1024:
            os.replace(out, path)
            return True, "remuxed to mp4"
        stderr_tail = proc.stderr[-500:].decode("utf-8", errors="replace") if proc.stderr else ""
        return False, f"ffmpeg remux failed (rc={proc.returncode}): {stderr_tail.strip()[-200:]}"
    except (OSError, subprocess.TimeoutExpired) as e:
        return False, f"ffmpeg remux failed ({type(e).__name__})"
    finally:
        if os.path.exists(out):
            try:
                os.remove(out)
            except OSError:
                pass


JAV_CODE_RE = re.compile(r'\b[A-Z]{2,6}-\d{1,6}\b')


def extract_jav_code(title, page_url=""):
    """Extract the release code (e.g. HMN-894) from the video title,
    falling back to the 'Code:' field on the video page."""
    m = JAV_CODE_RE.search(title or "")
    if m:
        return m.group(0)
    if page_url:
        parsed = urllib.parse.urlparse(page_url)
        if "jav.guru" not in parsed.netloc:
            # Stored page URLs are often proxy URLs; convert to upstream.
            page_url = BASE_URL + parsed.path + (f"?{parsed.query}" if parsed.query else "")
        page = fetch_url(page_url, referer=BASE_URL)
        if page:
            m = re.search(r'\bCode\b[\s\S]{0,200}?([A-Z]{2,6}-\d{1,6})', page)
            if m:
                return m.group(1)
    return None


def _other_active_prefixes(dl_id):
    """Working-filename prefixes of other in-flight downloads.

    Used by cleanup paths so deleting/cancelling one download never removes
    the partial file of a same-title download running under a unique base."""
    with download_lock:
        out = []
        for k, v in downloads.items():
            if k == dl_id or v.get("status") not in ("downloading", "queued"):
                continue
            b = v.get("base") or re.sub(r'[^\w\s\-]', '', v.get("title", ""))[:80].strip()
            if b:
                out.append(b)
        return out


def run_download(dl_id, url, title, fresh=True, _attempt=1):
    """Download a stream URL.

    Direct progressive MP4 (DD / cloudatacdn) is downloaded with curl, which
    has a standard TLS fingerprint and sends proper browser headers.
    HLS / DASH streams go through yt-dlp (fragment-parallel, remux, etc.).

    fresh=True (new download) removes any stale partial from an earlier
    attempt with the same title; fresh=False (resume) keeps it so the
    downloader can continue where it left off.  Transient network failures
    are retried up to MAX_DL_ATTEMPTS times with a re-resolved stream URL."""
    global downloads
    safe_title = re.sub(r'[^\w\s\-]', '', title)[:80].strip()
    if not safe_title:
        safe_title = f"video_{dl_id}"

    # Two concurrent downloads of the same title (e.g. the same video from
    # different providers) would otherwise write to — and, on `fresh`, delete —
    # the same file.  Give the working filename a unique suffix on collision;
    # _finish_download still renames the result to the release code.
    working = safe_title
    with download_lock:
        for k, v in downloads.items():
            if k == dl_id or v.get("status") not in ("downloading", "queued"):
                continue
            other = re.sub(r'[^\w\s\-]', '', v.get("title", ""))[:80].strip()
            if other == safe_title:
                working = f"{safe_title} [{dl_id}]"
                break
        if dl_id in downloads:
            downloads[dl_id]["base"] = working

    with download_lock:
        info = downloads.get(dl_id, {})
        page_url = info.get("page_url", "")
        provider = info.get("provider", "")
        resolution = info.get("resolution", "")
        other_files = {v.get("file") for v in downloads.values() if v.get("file")}
    code = extract_jav_code(title, page_url)

    # Prefer the provider-origin referer stored at download creation (e.g.
    # https://s1.maxstream.org/player/...).  Fall back to the upstream
    # jav.guru page URL so yt-dlp always sends a Referer header.
    referer = info.get("referer", "") or None
    if not referer and page_url:
        p = urllib.parse.urlparse(page_url)
        referer = BASE_URL + p.path + (("?" + p.query) if p.query else "")

    if fresh:
        for f in os.listdir(DOWNLOAD_DIR):
            fpath = os.path.join(DOWNLOAD_DIR, f)
            if f.startswith(working) or (code and fpath == os.path.join(DOWNLOAD_DIR, code + ".mp4") and fpath not in other_files):
                try:
                    os.remove(fpath)
                except OSError:
                    pass

    current_url = url
    use_ffmpeg = _needs_ffmpeg_hls(current_url)

    with download_lock:
        if use_ffmpeg:
            downloader = "ffmpeg"
        else:
            downloader = "yt-dlp"
        downloads[dl_id]["status"] = "downloading"
        downloads[dl_id]["progress"] = (
            f"Starting {downloader}..." if _attempt == 1 else
            f"Retry {_attempt - 1}/{MAX_DL_ATTEMPTS - 1} — starting {downloader}..."
        )

    if use_ffmpeg:
        output_path = os.path.join(DOWNLOAD_DIR, f"{working}.mp4")
        try:
            rc, lines = _download_file_ffmpeg(dl_id, current_url, output_path, referer)
        except Exception as e:
            rc, lines = 1, [f"ffmpeg failed to start: {e}"]
    else:
        is_hls = ".m3u8" in current_url.lower()
        output_template = os.path.join(DOWNLOAD_DIR, f"{working}.%(ext)s")
        cmd = [
            YTDLP,
            "--no-check-certificates",
            "--no-part",
            "--newline",
            "-N", "3",
            "-o", output_template,
        ]
        # Use aria2c for progressive MP4 (DoodStream/JK) to split into 3
        # segments.  Skip for HLS — yt-dlp's -N already handles fragment
        # parallelism and adding aria2c on top causes 429 rate limits.
        if not is_hls:
            cmd += ["--downloader", "aria2c:-x 16 -s 3 -j 3 -k 1M"]
        if referer:
            cmd += ["--referer", referer]
        cmd.append(current_url)
        try:
            rc, lines = _run_ytdlp_once(dl_id, cmd)
        except Exception as e:
            rc, lines = 1, [f"yt-dlp failed to start: {e}"]

    if rc == 0:
        _finish_download(dl_id, working, code)
        return

    tail = " | ".join(lines[-3:])

    # Transient network failures worth retrying (some CDNs, e.g. the DD
    # provider's cloudatacdn, intermittently reset connections).
    transient = any(TRANSIENT_NET_RE.search(l) for l in lines[-5:])
    if transient and _attempt < MAX_DL_ATTEMPTS:
        # Re-resolve the stream for a fresh token; a different URL means the
        # old partial file can't be continued, so remove it.
        new_url = current_url
        new_referer = referer
        if page_url:
            fmt = find_stream_for_resume(page_url, provider, resolution)
            if fmt and fmt.get("url"):
                new_url = fmt["url"]
                if fmt.get("_referer"):
                    new_referer = fmt["_referer"]
        if new_url != current_url:
            for f in os.listdir(DOWNLOAD_DIR):
                if f.startswith(working):
                    try:
                        os.remove(os.path.join(DOWNLOAD_DIR, f))
                    except OSError:
                        pass
            current_url = new_url
            referer = new_referer
            with download_lock:
                downloads[dl_id]["url"] = current_url
                if new_referer:
                    downloads[dl_id]["referer"] = new_referer
        with download_lock:
            downloads[dl_id]["progress"] = (
                f"Network error — retry {_attempt} of {MAX_DL_ATTEMPTS - 1} "
                f"in {5 * _attempt}s..."
            )
        time.sleep(5 * _attempt)
        with download_lock:
            if downloads.get(dl_id, {}).get("status") not in ("downloading", "queued"):
                return  # cancelled while waiting
        return run_download(dl_id, current_url, title, fresh=False, _attempt=_attempt + 1)

    with download_lock:
        downloads[dl_id]["status"] = "error"
        downloads[dl_id]["error"] = (
            f"{downloader} failed (rc {rc})" + (f": {tail}" if tail else "")
        )[:600]
        download_procs.pop(dl_id, None)
    save_state()
    log_update(dl_id, status="error", finished=_now())


# Retryable network failures seen in yt-dlp / ffmpeg / curl output.
TRANSIENT_NET_RE = re.compile(
    r"Connection (refused|reset|aborted)|timed ?out|Temporary failure in name"
    r" resolution|Could not resolve host|HTTP Error (408|429|5\d\d)"
    r"|remote end closed connection without sending|Network is unreachable"
    r"|Server returned 403 Forbidden|I/O error",
    re.I,
)
MAX_DL_ATTEMPTS = 3


def _is_direct_mp4_url(url):
    """True if the URL looks like a direct progressive MP4 (not m3u8/DASH)."""
    lower = url.lower()
    if ".m3u8" in lower:
        return False
    if "/master.m3u8" in lower or "/index.m3u8" in lower or ".mpd" in lower:
        return False
    return True


def _needs_ffmpeg_hls(url):
    """True if the HLS m3u8 URL needs ffmpeg (e.g. CDNs that 403 yt-dlp's
    generic extractor).  Other m3u8 providers work fine with yt-dlp."""
    lower = url.lower()
    if ".m3u8" not in lower:
        return False
    # The maxstream/tnmr/premilkyway CDN family uses the same infrastructure
    # (hls2/.../index-v1-a1.m3u8) and requires Referer+Origin on every HLS
    # sub-request.  yt-dlp's generic extractor doesn't propagate headers to
    # variant/segment fetches, so we use ffmpeg which sends -headers on all
    # requests.  Match on the URL path pattern rather than listing every domain.
    if "/hls2/" in lower:
        return True
    # AV (oppainet.net) serves extensionless segment URLs, which yt-dlp's
    # generic extractor cannot fetch at all; ffmpeg handles them once the
    # allowed_segment_extensions/extension_picky overrides below are set.
    if "oppainet.net" in lower:
        return True
    return False


FFMPEG_BIN = shutil.which("ffmpeg") or "ffmpeg"


def _download_file_ffmpeg(dl_id, url, output_path, referer=None):
    """Download an HLS stream using ffmpeg with proper headers.

    ffmpeg's HLS downloader sends the Referer/User-Agent for all requests
    (master playlist, variant playlists, and segment downloads), which
    bypasses yt-dlp's generic-extractor 403 issues on CDNs like maxstream.
    Returns (returncode, last_output_lines).
    """
    headers_str = ""
    if referer:
        headers_str += f"Referer: {referer}\r\n"
        # Some CDNs also check the Origin header (e.g. maxstream).
        try:
            rp = urllib.parse.urlparse(referer)
            origin = f"{rp.scheme}://{rp.netloc}"
            headers_str += f"Origin: {origin}\r\n"
        except Exception:
            pass
    # The LuluStream/tnmr CDN (STREAM LU) rejects requests that don't send
    # Accept-Language, and also blocks ffmpeg's default "Lavf/..." User-Agent.
    # -headers *adds* headers, so passing User-Agent there leaves Lavf as the
    # first UA; -user_agent replaces the default instead.
    headers_str += "Accept-Language: en-US,en;q=0.5\r\n"

    cmd = [
        FFMPEG_BIN,
        "-y",
        "-hide_banner",
        "-user_agent", _BROWSERS_UA,
        "-headers", headers_str,
        # AV (oppainet.net) segments are served from extensionless URLs, which
        # the HLS demuxer rejects unless we widen the allow-list and disable
        # the "extension must match" strictness.
        "-allowed_segment_extensions", "ALL",
        "-extension_picky", "false",
        "-i", url,
        "-c", "copy",
        "-bsf:a", "aac_adtstoasc",
        "-movflags", "+faststart",
        output_path,
    ]

    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, bufsize=1,
    )
    with download_lock:
        download_procs[dl_id] = proc

    lines = []
    for line in proc.stdout:
        line = line.strip()
        if not line or _FFMPEG_NOISE_RE.match(line):
            continue
        lines.append(line)
        with download_lock:
            downloads[dl_id]["progress"] = line

    proc.wait()
    return proc.returncode, lines


# ffmpeg logs one "Opening '...' for reading" line per HLS segment (plus TCP
# connection chatter).  These flood the progress field and make a healthy
# download look like it is stuck connecting, so drop them and let the periodic
# stats line ("frame=... time=... speed=...") drive the display.
_FFMPEG_NOISE_RE = re.compile(
    r"^\[[^\]]+ @ 0x[0-9a-f]+\] "
    r"(Opening '.*' for reading|Starting connection attempt to"
    r"|Successfully connected to|Skip \('#EXT-X-.*'\))"
)


CURL_BIN = shutil.which("curl") or "curl"
_BROWSERS_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)


def _download_file_curl(dl_id, url, output_path, referer=None):
    """Download a direct MP4 using curl.

    curl has better TLS handling than yt-dlp's generic extractor and sends
    browser-like headers by default.  Returns (returncode, last_output_lines).
    """
    cmd = [
        CURL_BIN,
        "-L",                        # follow redirects
        "-k",                        # ignore TLS errors (--insecure)
        "-o", output_path,
        "-H", f"User-Agent: {_BROWSERS_UA}",
        "-H", "Accept: video/mp4,*/*;q=0.9",
        "-H", "Accept-Language: en-US,en;q=0.5",
        "--connect-timeout", "20",
        "--max-time", "3600",         # 1 h hard limit
        "--retry", "2",
        "--retry-delay", "5",
        "--retry-all-errors",
        "-f",                        # fail silently on HTTP errors
    ]
    if referer:
        cmd += ["-H", f"Referer: {referer}"]
    cmd.append(url)

    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, bufsize=1,
    )
    with download_lock:
        download_procs[dl_id] = proc

    lines = []
    for line in proc.stdout:
        line = line.strip()
        if line:
            lines.append(line)
            with download_lock:
                downloads[dl_id]["progress"] = line

    proc.wait()
    return proc.returncode, lines


def _run_ytdlp_once(dl_id, cmd):
    """Run yt-dlp to completion; returns (returncode, output lines)."""
    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, bufsize=1
    )
    # Store the process handle so it can be cancelled mid-download
    with download_lock:
        download_procs[dl_id] = proc

    lines = []
    for line in proc.stdout:
        line = line.strip()
        if line:
            lines.append(line)
            with download_lock:
                downloads[dl_id]["progress"] = line

    proc.wait()
    return proc.returncode, lines


def _finish_download(dl_id, base, code):
    """Success path: locate the file, validate, remux, rename, mark done."""
    # Find the downloaded file: only a plain "<base>.<ext>" match —
    # never yt-dlp helper files (.ytdl, -FragN) or our .remux.mp4.
    # If several match (retries with different containers), take the largest.
    fpath = None
    for f in os.listdir(DOWNLOAD_DIR):
        if not f.startswith(base + "."):
            continue
        ext = f[len(base) + 1:]
        if "." in ext or "-" in ext or not ext.isalnum():
            continue
        cand = os.path.join(DOWNLOAD_DIR, f)
        if fpath is None or os.path.getsize(cand) > os.path.getsize(fpath):
            fpath = cand
    if fpath is None:
        with download_lock:
            downloads[dl_id]["status"] = "done"
            downloads[dl_id]["progress"] = "Complete (file not found on disk)"
            download_procs.pop(dl_id, None)
        save_state()
        log_update(dl_id, status="done", finished=_now())
        return
    if not looks_like_video(fpath):
        # Provider served an image/error page, not video.
        try:
            os.remove(fpath)
        except OSError:
            pass
        with download_lock:
            downloads[dl_id]["status"] = "error"
            downloads[dl_id]["error"] = "Downloaded file is not a video (provider served an error image)"
            download_procs.pop(dl_id, None)
        save_state()
        log_update(dl_id, status="error", finished=_now())
        return
    # Remux PNG+TS payloads into a clean MP4 container.
    with download_lock:
        downloads[dl_id]["progress"] = "Finalizing (remuxing to MP4)..."
    ok, msg = finalize_video(fpath)
    if not ok:
        try:
            os.remove(fpath)
        except OSError:
            pass
        with download_lock:
            downloads[dl_id]["status"] = "error"
            downloads[dl_id]["error"] = f"Downloaded file is not playable video ({msg})"
            download_procs.pop(dl_id, None)
        save_state()
        log_update(dl_id, status="error", finished=_now())
        return
    # Clean up any leftover yt-dlp helper files for this title.
    for f in os.listdir(DOWNLOAD_DIR):
        if f.startswith(base + ".") and f != os.path.basename(fpath):
            try:
                os.remove(os.path.join(DOWNLOAD_DIR, f))
            except OSError:
                pass
    # Rename to the release code (e.g. HMN-894.mp4) so the Save file
    # button downloads with a clean filename.
    if code:
        # Choose a free target and reserve it under the lock, so two downloads
        # finishing at the same moment can't both claim "<code>.mp4".  A stale
        # file with the same code (not owned by another download) is replaced.
        with download_lock:
            owned = {v.get("file") for k, v in downloads.items()
                     if k != dl_id and v.get("file")}
            target = os.path.join(DOWNLOAD_DIR, code + ".mp4")
            if os.path.exists(target) and target not in owned:
                try:
                    os.remove(target)
                except OSError:
                    pass
            n = 2
            while os.path.exists(target) or target in owned:
                target = os.path.join(DOWNLOAD_DIR, f"{code} ({n}).mp4")
                n += 1
            downloads[dl_id]["file"] = target
        if os.path.abspath(target) != os.path.abspath(fpath):
            try:
                os.replace(fpath, target)
                fpath = target
            except OSError:
                pass
    with download_lock:
        downloads[dl_id]["status"] = "done"
        downloads[dl_id]["file"] = fpath
        downloads[dl_id]["code"] = code
        downloads[dl_id]["progress"] = "Complete"
        download_procs.pop(dl_id, None)
    save_state()
    log_update(dl_id, status="done", code=code, finished=_now())


# ── Downloads page ──────────────────────────────────────────────────────────

def render_log_page():
    with log_lock:
        entries = list(reversed(_load_log()))
    rows = []
    for e in entries:
        status = str(e.get("status") or "")
        page_url = str(e.get("page_url") or "")
        source_html = ""
        if page_url:
            source_html = f'<a href="{html.escape(page_url)}" target="_blank" style="color:#2196f3;font-size:11px;text-decoration:none;" title="{html.escape(page_url)}">source</a>'
        rows.append(
            "<tr>"
            f"<td>{html.escape(str(e.get('id', '')))}</td>"
            f"<td class='title'>{html.escape(str(e.get('title') or ''))}</td>"
            f"<td class='provider'>{html.escape(str(e.get('provider') or ''))}</td>"
            f"<td>{html.escape(str(e.get('resolution') or ''))}</td>"
            f"<td class='ts'>{html.escape(str(e.get('started') or ''))}</td>"
            f"<td class='ts'>{html.escape(str(e.get('finished') or '—'))}</td>"
            f"<td class='status {html.escape(status)}'>{html.escape(status)}</td>"
            f"<td>{html.escape(str(e.get('code') or ''))}</td>"
            f"<td>{source_html}</td>"
            "</tr>"
        )
    if not rows:
        rows.append("<tr><td colspan='9' style='color:#666'>No downloads logged yet.</td></tr>")
    return LOG_PAGE.replace("__ROWS__", "\n".join(rows)).replace(
        "__COUNT__", str(len(entries)))


LOG_PAGE = """<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Download Log - JavProxy</title>
<style>
body { background:#0f0f1a; color:#eee; font-family:Arial,sans-serif; margin:0; padding:20px; }
h1 { color:#e94560; font-size:20px; margin:0 0 16px 0; }
h1 a { color:#2196f3; font-size:13px; font-weight:normal; text-decoration:none; margin-left:10px; }
h1 a:hover { text-decoration:underline; }
table { width:100%; border-collapse:collapse; }
th,td { text-align:left; padding:10px 8px; border-bottom:1px solid #23233a; font-size:13px; vertical-align:middle; }
th { color:#888; text-transform:uppercase; font-size:11px; }
.status { font-weight:bold; }
.done { color:#4caf50; } .error { color:#ff6b6b; }
.interrupted { color:#ff9800; } .cancelled { color:#888; } .queued { color:#ff9800; }
.title { color:#ccc; }
.provider { color:#aaa; font-size:12px; white-space:nowrap; }
.ts { color:#aaa; font-size:12px; white-space:nowrap; }
.hint { color:#555; font-size:11px; margin-top:12px; }
</style>
</head>
<body>
<h1>Download Log <a href="/downloads">&larr; Downloads</a></h1>
<table>
<thead><tr><th>#</th><th>Title</th><th>Provider</th><th>Res</th><th>Started</th><th>Finished</th><th>Status</th><th>Code</th><th>Source</th></tr></thead>
<tbody>
__ROWS__
</tbody>
</table>
<div class="hint">Permanent history of __COUNT__ download(s). Entries remain here after a download is deleted.</div>
</body>
</html>
"""


DOWNLOADS_PAGE = """<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Downloads - JavProxy</title>
<style>
body { background:#0f0f1a; color:#eee; font-family:Arial,sans-serif; margin:0; padding:20px; }
h1 { color:#e94560; font-size:20px; margin:0 0 16px 0; }
h1 a { color:#2196f3; font-size:13px; font-weight:normal; text-decoration:none; margin-left:10px; }
h1 a:hover { text-decoration:underline; }
table { width:100%; border-collapse:collapse; }
th,td { text-align:left; padding:10px 8px; border-bottom:1px solid #23233a; font-size:13px; vertical-align:middle; }
th { color:#888; text-transform:uppercase; font-size:11px; }
.status { font-weight:bold; }
.done { color:#4caf50; } .downloading { color:#2196f3; } .queued { color:#ff9800; }
.error { color:#ff6b6b; } .interrupted { color:#ff9800; } .cancelled { color:#888; }
button, a.btn { display:inline-block; padding:6px 12px; border-radius:6px; border:1px solid #e94560;
  background:#0f3460; color:#fff; font-size:12px; cursor:pointer; text-decoration:none; margin-right:6px; }
button:hover, a.btn:hover { background:#16437e; }
button.del { border-color:#ff6b6b; }
button.del:hover { background:#6b2121; }
.progress { color:#888; font-size:12px; max-width:340px; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
.title { color:#ccc; }
.provider { color:#aaa; font-size:12px; white-space:nowrap; }
.hint { color:#555; font-size:11px; margin-top:12px; }
</style>
</head>
<body>
<h1>Downloads <a href="/log">Log</a></h1>
<table>
<thead><tr><th>Title</th><th>Provider</th><th>Source</th><th>Status</th><th>Progress</th><th></th></tr></thead>
<tbody id="rows"></tbody>
</table>
<div class="hint">Auto-refreshes every 2s. Completed files can be saved at any time, even after a server restart.</div>
<script>
function esc(s) { const d = document.createElement('div'); d.textContent = s || ''; return d.innerHTML; }

async function cancelDl(btn) {
  btn.disabled = true;
  await fetch('/api/download/' + btn.dataset.id, { method: 'DELETE' });
  refresh();
}

async function resumeDl(btn) {
  btn.disabled = true; btn.textContent = 'Resolving...';
  const r = await fetch('/api/download/resume', {
    method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ id: btn.dataset.id })
  });
  const d = await r.json();
  if (d.error) { alert(d.error); btn.disabled = false; btn.textContent = 'Resume'; }
  refresh();
}

async function deleteDl(btn) {
  if (!confirm('Delete this download (and its files) from the server?')) return;
  btn.disabled = true;
  const r = await fetch('/api/file/' + btn.dataset.id, { method: 'DELETE' });
  if (!r.ok) { alert('Delete failed'); btn.disabled = false; return; }
  refresh();
}

async function refresh() {
  try {
    const resp = await fetch('/api/downloads');
    const data = await resp.json();
    const rows = document.getElementById('rows');
    const ids = Object.keys(data).sort((a, b) => b - a);
    rows.innerHTML = '';
    if (!ids.length) {
      rows.innerHTML = '<tr><td colspan="6" style="color:#666">No downloads yet.</td></tr>';
    }
    for (const id of ids) {
      const d = data[id];
      let actions = '';
      if (d.status === 'downloading' || d.status === 'queued') {
        actions = '<button data-id="' + id + '" onclick="cancelDl(this)">Cancel</button>';
      } else if (d.status === 'done') {
        actions = '<a class="btn" href="/api/file/' + id + '">Save file</a>' +
                  '<button class="del" data-id="' + id + '" onclick="deleteDl(this)">Delete</button>';
      } else if (d.status === 'interrupted' || d.status === 'error' || d.status === 'cancelled') {
        if (d.resumable) {
          actions += '<button data-id="' + id + '" onclick="resumeDl(this)">Resume</button>';
        }
        actions += '<button class="del" data-id="' + id + '" onclick="deleteDl(this)">Delete</button>';
      }
      const tr = document.createElement('tr');
      const detail = (d.status === 'error' && d.error) ? d.error : (d.progress || d.error || '');
      const sourceHtml = d.page_url
        ? '<a href="' + esc(d.page_url) + '" target="_blank" style="color:#2196f3;font-size:11px;text-decoration:none;" title="' + esc(d.page_url) + '">source</a>'
        : '';
      tr.innerHTML =
        '<td class="title">' + esc(d.title || 'download ' + id) + '</td>' +
        '<td class="provider">' + esc(d.provider || '') + '</td>' +
        '<td>' + sourceHtml + '</td>' +
        '<td class="status ' + esc(d.status) + '">' + esc(d.status) + '</td>' +
        '<td class="progress" title="' + esc(detail) + '">' + esc(detail) + '</td>' +
        '<td>' + actions + '</td>';
      rows.appendChild(tr);
    }
  } catch (e) { /* server unreachable; keep retrying */ }
  setTimeout(refresh, 2000);
}

refresh();
</script>
</body>
</html>
"""


# ── HTTP Handler ────────────────────────────────────────────────────────────

class ProxyHandler(http.server.BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        """Log errors but suppress routine access logs."""
        msg = format % args
        if "error" in msg.lower() or "traceback" in msg.lower():
            sys.stderr.write(msg + "\n")

    def _auth_ok(self):
        """Basic auth gate. Returns True if auth is disabled or the
        Authorization header matches BASIC_AUTH_USER/BASIC_AUTH_PASS."""
        if not BASIC_AUTH_USER or not BASIC_AUTH_PASS:
            return True
        expected = "Basic " + base64.b64encode(
            f"{BASIC_AUTH_USER}:{BASIC_AUTH_PASS}".encode()
        ).decode()
        provided = self.headers.get("Authorization", "")
        if hmac.compare_digest(provided, expected):
            return True
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="JavProxy"')
        self.send_header("Content-Length", "0")
        self.end_headers()
        return False

    def do_GET(self):
        if not self._auth_ok():
            return
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = parsed.query

        # ── API: List parseable hosts ──
        if path == "/api/hosts":
            params = urllib.parse.parse_qs(query)
            url = params.get("url", [None])[0]
            if not url:
                self.send_json(400, {"error": "Missing url parameter"})
                return
            parsed_url = urllib.parse.urlparse(url)
            upstream_path = parsed_url.path
            if parsed_url.query:
                upstream_path += "?" + parsed_url.query
            self.send_json(200, list_page_hosts(BASE_URL + upstream_path))
            return

        # ── API: Parse streams ──
        if path == "/api/parse":
            params = urllib.parse.parse_qs(query)
            url = params.get("url", [None])[0]
            provider = params.get("provider", [None])[0]
            if not url:
                self.send_json(400, {"error": "Missing url parameter"})
                return

            # The frontend sends the proxy URL (e.g. http://192.168.x.x:8080/...).
            # Convert it back to the upstream jav.guru URL.
            parsed_url = urllib.parse.urlparse(url)
            upstream_path = parsed_url.path
            if parsed_url.query:
                upstream_path += "?" + parsed_url.query
            url = BASE_URL + upstream_path

            result = extract_streams_from_page(url, provider)
            self.send_json(200, result)
            return

        # ── API: Download status ──
        if path.startswith("/api/download/"):
            dl_id = path.split("/")[-1]
            with download_lock:
                info = downloads.get(dl_id, {"status": "not found"})
            self.send_json(200, info)
            return

        # ── API: Serve downloaded file ──
        if path.startswith("/api/file/"):
            dl_id = path.split("/")[-1]
            with download_lock:
                info = downloads.get(dl_id, {})
            file_path = info.get("file")
            if file_path and os.path.exists(file_path):
                filename = os.path.basename(file_path)
                self.send_response(200)
                self.send_header("Content-Type", "application/octet-stream")
                self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
                file_size = os.path.getsize(file_path)
                self.send_header("Content-Length", str(file_size))
                self.end_headers()
                with open(file_path, "rb") as f:
                    shutil.copyfileobj(f, self.wfile)
            else:
                self.send_json(404, {"error": "File not found"})
            return

        # ── API: List downloads ──
        if path == "/api/downloads":
            with download_lock:
                result = {k: dict(v) for k, v in downloads.items()}
            for v in result.values():
                v["resumable"] = (
                    v.get("status") in ("interrupted", "error", "cancelled")
                    and bool(v.get("page_url"))
                )
            self.send_json(200, result)
            return

        # ── Downloads monitoring page ──
        if path == "/downloads":
            body = DOWNLOADS_PAGE.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-cache")
            self.end_headers()
            self.wfile.write(body)
            return

        # ── Download log page ──
        if path == "/log":
            body = render_log_page().encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-cache")
            self.end_headers()
            self.wfile.write(body)
            return

        # ── Proxy CDN assets ──
        if path.startswith("/cdn/"):
            cdn_provider = path.split("/")[2] if len(path.split("/")) > 2 else ""
            if cdn_provider == "javmiku":
                suffix = path[len('/cdn/javmiku'):]
                real_url = "https://cdn.javmiku.com" + suffix
            elif cdn_provider == "javnorth":
                suffix = path[len('/cdn/javnorth'):]
                real_url = "https://cdn.javnorth.com" + suffix
            else:
                self.send_error(404)
                return

            # Fetch binary content (images, CSS, JS) with proper Referer
            data, remote_ct = fetch_url_bytes(real_url, referer=BASE_URL)
            if data is None:
                self.send_error(502)
                return

            # Determine Content-Type from extension (overrides CDN header)
            content_type = "application/octet-stream"
            if ".png" in path:
                content_type = "image/png"
            elif ".jpg" in path or ".jpeg" in path or ".webp" in path:
                content_type = "image/jpeg"
            elif ".css" in path:
                content_type = "text/css"
            elif ".js" in path:
                content_type = "application/javascript"
            elif ".woff" in path or ".woff2" in path:
                content_type = "font/woff2"
            elif ".gif" in path:
                content_type = "image/gif"
            elif ".svg" in path:
                content_type = "image/svg+xml"

            self.send_response(200)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "public, max-age=86400")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()
            self.wfile.write(data)
            return

        # ── Proxy jav.guru pages ──
        # Build the real URL
        real_url = BASE_URL + path
        if query:
            real_url += "?" + query

        content = fetch_url(real_url, referer=BASE_URL)
        if content is None:
            self.send_error(502, "Failed to fetch upstream")
            return

        # Determine if this is HTML
        is_html = True  # Default assumption for jav.guru
        content_type_header = "text/html; charset=utf-8"

        if is_html:
            # Strip ads
            content = strip_ads_from_html(content, real_url)

            # Inject parse button on video pages
            content = inject_parse_button(content, real_url)

            # Inject a floating "Downloads" badge on every page, linking to
            # the download monitor.
            badge = (
                '<a id="javproxy-dl-badge" href="/downloads" style="'
                'position:fixed;top:10px;left:10px;z-index:1000000;'
                'background:#0f3460;color:#fff;border:1px solid #e94560;'
                'border-radius:16px;padding:6px 14px;font:bold 12px Arial,sans-serif;'
                'text-decoration:none;box-shadow:0 4px 12px rgba(0,0,0,.4);">'
                'Downloads</a>'
            )
            if '</body>' in content:
                content = content.replace('</body>', badge + '\n</body>', 1)
            else:
                content += badge

            # Build the proxy prefix from the incoming Host header so images
            # and links work correctly when accessed over LAN.
            host = self.headers.get("Host", f"localhost:{LISTEN_PORT}")
            proxy_prefix = f"http://{host}"
            content = rewrite_urls(content, proxy_prefix)

            # Fix relative URLs for CSS/JS and form actions
            content = re.sub(
                r"""(href|src|action)=(['"])(/[^'"]+)\2""",
                lambda m: f'{m.group(1)}={m.group(2)}{proxy_prefix}{m.group(3)}{m.group(2)}',
                content
            )

            if isinstance(content, str):
                content = content.encode("utf-8")

        self.send_response(200)
        self.send_header("Content-Type", content_type_header)
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(content)

    def do_DELETE(self):
        if not self._auth_ok():
            return
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path

        # ── Delete a completed file from disk ──
        if path.startswith("/api/file/"):
            dl_id = path.split("/")[-1]
            with download_lock:
                info = downloads.get(dl_id)
            if not info:
                self.send_json(404, {"error": "Download not found"})
                return
            file_path = info.get("file")
            if file_path and os.path.exists(file_path):
                try:
                    os.remove(file_path)
                except OSError as e:
                    self.send_json(500, {"error": f"Failed to delete file: {e}"})
                    return
            # Remove any leftover partial/helper files for this title,
            # without touching files that belong to other download entries.
            base = info.get("base") or re.sub(r'[^\w\s\-]', '', info.get("title", ""))[:80].strip()
            with download_lock:
                other_files = {v.get("file") for v in downloads.values() if v.get("file")}
            protect = _other_active_prefixes(dl_id)
            if base:
                for f in os.listdir(DOWNLOAD_DIR):
                    fpath = os.path.join(DOWNLOAD_DIR, f)
                    if fpath in other_files:
                        continue
                    if f.startswith(base) and not any(f.startswith(p) for p in protect):
                        try:
                            os.remove(fpath)
                        except OSError:
                            pass
            with download_lock:
                download_procs.pop(dl_id, None)
                downloads.pop(dl_id, None)
            save_state()
            self.send_json(200, {"status": "deleted", "id": dl_id})
            return

        # ── Cancel / delete a download ──
        if path.startswith("/api/download/"):
            dl_id = path.split("/")[-1]
            with download_lock:
                info = downloads.get(dl_id)

            if not info:
                self.send_json(404, {"error": "Download not found"})
                return

            # Kill the subprocess if still running
            proc = download_procs.get(dl_id)
            if proc and proc.poll() is None:
                try:
                    proc.terminate()
                    try:
                        proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                except Exception:
                    pass

            # Delete partial file + fragments from disk
            base = info.get("base") or re.sub(r'[^\w\s\-]', '', info.get("title", ""))[:80].strip()
            protect = _other_active_prefixes(dl_id)
            if base:
                for f in os.listdir(DOWNLOAD_DIR):
                    if f.startswith(base) and not any(f.startswith(p) for p in protect):
                        try:
                            os.remove(os.path.join(DOWNLOAD_DIR, f))
                        except OSError:
                            pass

            with download_lock:
                downloads[dl_id]["status"] = "cancelled"
                downloads[dl_id]["progress"] = "Cancelled by user"
                download_procs.pop(dl_id, None)
            save_state()
            log_update(dl_id, status="cancelled", finished=_now())

            self.send_json(200, {"status": "cancelled", "id": dl_id})
            return

        self.send_error(404)

    def do_POST(self):
        if not self._auth_ok():
            return
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path

        if path == "/api/download":
            content_length = int(self.headers.get("Content-Length", 0))
            body = self.rfile.read(content_length)
            try:
                data = json.loads(body)
            except json.JSONDecodeError:
                self.send_json(400, {"error": "Invalid JSON"})
                return

            url = data.get("url")
            title = data.get("title", "video")
            if not url:
                self.send_json(400, {"error": "Missing url"})
                return

            global download_counter
            download_counter += 1
            dl_id = str(download_counter)

            with download_lock:
                downloads[dl_id] = {
                    "status": "queued",
                    "progress": "Waiting...",
                    "file": None,
                    "title": title,
                    "error": None,
                    "url": url,
                    # Resume metadata: lets us re-resolve the stream after a
                    # restart or expired token and continue the download.
                    "page_url": data.get("page_url", ""),
                    "provider": data.get("provider", ""),
                    "resolution": data.get("resolution", ""),
                    "referer": data.get("referer", ""),
                }
            save_state()
            log_add(dl_id, title, data.get("provider", ""), data.get("resolution", ""), data.get("page_url", ""))

            # Start download in background thread
            t = threading.Thread(target=run_download, args=(dl_id, url, title), daemon=True)
            t.start()

            self.send_json(200, {"id": dl_id, "status": "queued"})
            return

        # ── API: Resume an interrupted/failed download ──
        if path == "/api/download/resume":
            content_length = int(self.headers.get("Content-Length", 0))
            body = self.rfile.read(content_length)
            try:
                data = json.loads(body)
            except json.JSONDecodeError:
                self.send_json(400, {"error": "Invalid JSON"})
                return
            dl_id = str(data.get("id", ""))
            with download_lock:
                info = downloads.get(dl_id)
            if not info:
                self.send_json(404, {"error": "Download not found"})
                return
            if info.get("status") not in ("interrupted", "error", "cancelled"):
                self.send_json(400, {"error": f"Cannot resume a download in status '{info.get('status')}'"})
                return
            if info.get("status") == "downloading":
                self.send_json(400, {"error": "Already downloading"})
                return

            # Re-resolve the stream: re-parse the video page and pick the same
            # provider + resolution. Fall back to the stored URL if the page
            # can no longer be parsed.
            old_url = info.get("url", "")
            new_url = old_url
            fmt = find_stream_for_resume(
                info.get("page_url", ""), info.get("provider", ""), info.get("resolution", "")
            )
            if fmt:
                new_url = fmt["url"]

            # A different stream URL means the old partial file can't be
            # continued (new token/CDN path) — remove it so yt-dlp starts clean.
            if new_url != old_url:
                base = info.get("base") or re.sub(r'[^\w\s\-]', '', info.get("title", ""))[:80].strip()
                protect = _other_active_prefixes(dl_id)
                if base:
                    for f in os.listdir(DOWNLOAD_DIR):
                        if f.startswith(base) and not any(f.startswith(p) for p in protect):
                            try:
                                os.remove(os.path.join(DOWNLOAD_DIR, f))
                            except OSError:
                                pass

            # Update referer from the freshly-resolved format so yt-dlp
            # sends the correct provider-origin Referer header.
            fresh_referer = fmt.get("_referer", "") if fmt else ""

            with download_lock:
                downloads[dl_id].update({
                    "status": "queued",
                    "progress": "Resuming — re-resolving stream...",
                    "error": None,
                    "file": None,
                    "url": new_url,
                    **({"referer": fresh_referer} if fresh_referer else {}),
                })
            save_state()
            log_update(dl_id, status="queued", finished=None)

            t = threading.Thread(target=run_download, args=(dl_id, new_url, info.get("title", "video"), False), daemon=True)
            t.start()
            self.send_json(200, {"id": dl_id, "status": "queued", "resumed": True})
            return

        self.send_error(404)

    def send_json(self, code, data):
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(body)


# ── Main ────────────────────────────────────────────────────────────────────

def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else LISTEN_PORT
    threading.Thread(target=_state_saver_loop, daemon=True).start()
    server = http.server.ThreadingHTTPServer(("0.0.0.0", port), ProxyHandler)
    print(f"""
╔══════════════════════════════════════════════════╗
║         JavProxy - Ad-Free Stream Proxy         ║
╠══════════════════════════════════════════════════╣
║                                                  ║
║  Open:  http://localhost:{port}                    ║
║  Browse: http://localhost:{port}/                  ║
║                                                  ║
║  Downloads saved to:                             ║
║  {DOWNLOAD_DIR:<44s} ║
║                                                  ║
╚══════════════════════════════════════════════════╝
""")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down...")
        server.shutdown()


if __name__ == "__main__":
    main()
