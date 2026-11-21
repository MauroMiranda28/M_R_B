# Build from this folder: docker build -t my-bot .
# The match runs it with no network, a read-only root (writable /tmp), 1 CPU, 512 MB, and the map at /arena.
FROM python:3.13.5-slim-bookworm
ENV PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
WORKDIR /bot
COPY mechfight.py bot.py nav.bin roofspots.json ./
RUN python3 -m py_compile /bot/bot.py /bot/mechfight.py && chmod -R a+rX /bot
ENTRYPOINT ["python3", "-u", "/bot/bot.py"]
