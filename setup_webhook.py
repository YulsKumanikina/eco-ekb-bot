# setup_webhook.py
import requests

# --- Импортируем токен из config.py ---
try:
    from config import TELEGRAM_TOKEN
except ImportError:
    print("Ошибка: не удалось найти файл config.py или переменную TELEGRAM_TOKEN в нем.")
    exit()

# --- Запрашиваем URL у пользователя ---
# Этот URL нужно скопировать из окна запущенного Ngrok (строка Forwarding, которая начинается с https://)
ngrok_url = input("Введите ваш Ngrok URL (например, https://abcd-123.ngrok-free.app): ")

if not ngrok_url.startswith("https://"):
    print("Ошибка: URL должен начинаться с https://")
    exit()

# Составляем полный адрес для вебхука
webhook_url = f"{ngrok_url.strip()}/telegram"

# Отправляем запрос к API Telegram для установки вебхука
api_url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/setWebhook"
response = requests.post(api_url, json={"url": webhook_url})

# Печатаем результат
print("\n--- Результат настройки вебхука ---")
print(f"Отправлен запрос на установку вебхука: {webhook_url}")
print(f"Ответ от Telegram:")
print(response.json())

if response.json().get("ok"):
    print("\n✅ Вебхук успешно установлен!")
else:
    print("\n❌ Ошибка при установке вебхука. Проверьте токен и URL.")