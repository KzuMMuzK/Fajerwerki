FROM python:3.11-slim

ENV PYTHONDONTWRITEBYTECODE=1
ENV PYTHONUNBUFFERED=1

# Instalacja pakietów systemowych z apt.txt (Tesseract i języki)
COPY apt.txt /tmp/apt.txt
RUN apt-get update && apt-get install -y --no-install-recommends \
    $(cat /tmp/apt.txt | tr '\n' ' ') \
    libgl1 \
    libglib2.0-0 \
    && rm -rf /var/lib/apt/lists/* \
    && rm /tmp/apt.txt

WORKDIR /app

# Instalacja zależności Pythona
COPY requirements.txt .
RUN pip install --no-cache-dir --upgrade pip && \
    pip install --no-cache-dir -r requirements.txt

# Kopiowanie reszty kodu (z wyłączeniem folderu site, jeśli chcesz)
COPY . .

EXPOSE 8080

# Uruchomienie Gunicorna – app.py zawiera obiekt 'app'
CMD ["gunicorn", "--bind", "0.0.0.0:8080", "--workers", "2", "--threads", "4", "app:app"]
