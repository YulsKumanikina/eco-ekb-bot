# delete_webhook.py
import requests

try:
    from config import TELEGRAM_TOKEN
except ImportError:
    print("Ошибка: не удалось найти файл config.py или переменную TELEGRAM_TOKEN.")
    exit()

# Формируем URL для вызова метода deleteWebhook
api_url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/deleteWebhook"

# Отправляем запрос
response = requests.post(api_url, json={"drop_pending_updates": True})

# Печатаем результат
print("--- Результат сброса вебхука ---")
if response.json().get("ok"):
    print("✅ Вебхук успешно удален!")
else:
    print("❌ Ошибка при удалении вебхука:")

print(response.json())