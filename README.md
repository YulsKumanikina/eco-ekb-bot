🌱 Эко-Помощник - Telegram Bot
     
Умный Telegram-бот для помощи в сортировке отходов, поиске пунктов приема вторсырья и обучения экологичному образу жизни с элементами геймификации.
✨ Особенности
•	🔍 Интеллектуальный поиск пунктов приема по видам отходов
•	💬 AI-помощник на базе GigaChat для ответов на вопросы
•	🎮 Геймификация с уровнями, достижениями и лидербордом
•	📱 Удобный интерфейс с кнопками и инлайн-меню
•	🌍 Поддержка multiple городов и материалов
🚀 Быстрый старт
Предварительные требования
•	Python 3.8+
•	Telegram Bot Token
•	GigaChat API ключ (опционально)
Установка
1.	Клонируйте репозиторий
git clone https://github.com/your-username/eco-assistant-bot.git
cd eco-assistant-bot

Установите зависимости
pip install -r requirements.txt

Настройте конфигурацию
cp config.example.py config.py
# Отредактируйте config.py своими ключами

Запустите бота
python bot_polling.py

📁 Структура проекта
eco-bot/
├── bot_polling.py          # Основной файл бота
├── config.py               # Конфигурация (не в репозитории)
├── db_manager.py           # Управление БД
├── challenges_data.py      # Эко-челленджи
├── requirements.txt        # Зависимости
└── data/                   # Данные
    ├── knowledge_base.json
    ├── recycling_points.csv
    ├── interesting_facts.json
    └── eco_tips.json

🎮 Использование
Основные команды:
/start - начать работу

/help - помощь и инструкция

/profile - ваш профиль

/leaderboard - таблица лидеров

Основные кнопки:
♻️ Найти пункт приема

✅ Я сдал вторсырье

🧠 Эко-викторина

💪 Эко-челлендж

👤 Мой профиль

🤝 Разработка
Добавление новых пунктов приема
Отредактируйте data/recycling_points.csv в формате:
name,city,address,accepts,work_hours,phone_number,website

Добавление вопросов в базу знаний
Используйте convert_kb.py для конвертации CSV в JSON или редактируйте knowledge_base.json напрямую.

