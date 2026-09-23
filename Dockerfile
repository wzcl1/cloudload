FROM python:3.12-slim

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    YTDLP=yt-dlp \
    LISTEN_PORT=8080

# ffmpeg remuxes TS-payload downloads (served as .mp4) into clean MP4 files.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ffmpeg \
        aria2 \
        ca-certificates \
        curl \
    && rm -rf /var/lib/apt/lists/*

# yt-dlp for downloading the resolved stream URLs.
RUN pip install --no-cache-dir --upgrade pip yt-dlp

WORKDIR /app
COPY proxy.py ./
RUN mkdir -p /app/downloads

EXPOSE 8080

CMD ["python", "proxy.py", "8080"]
