# =========================================================================
# ===    BOT_POLLING.PY (ФИНАЛЬНАЯ ВЕРСИЯ 2.0 - СТАБИЛЬНАЯ)           ===
# =========================================================================

import telebot
from telebot import types 
import pandas as pd
import json
import re
from typing import List, Tuple
from gigachat.client import GigaChatSyncClient
from gigachat.models import Chat, Messages, MessagesRole
import random
from datetime import datetime, date, timedelta
import logging
from collections import deque
from thefuzz import process
import os

import db_manager as db
import challenges_data as challenges
from apscheduler.schedulers.background import BackgroundScheduler



BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# --- НАСТРОЙКА ЛОГИРОВАНИЯ ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler()]
)

# --- ГЛОБАЛЬНЫЕ НАСТРОЙКИ ---
user_context = {}
MAX_HISTORY_LENGTH = 5

# ### НАСТРОЙКИ ГЕЙМИФИКАЦИИ ###
POINTS_FOR_RECYCLE = 10; POINTS_FOR_STREAK = 50; POINTS_FOR_CHALLENGE = 75;
POINTS_FOR_QUIZ = 5; POINTS_FOR_TIP = 1; POINTS_FOR_INVITE = 30; POINTS_FOR_ACHIEVEMENT = 20;

LEVELS = {
    1: {"name": "Новичок", "min_points": 0}, 2: {"name": "Осознанный житель", "min_points": 100},
    3: {"name": "Эко-активист", "min_points": 250}, 4: {"name": "Страж Природы", "min_points": 500},
    5: {"name": "Эко-Воин", "min_points": 1000},
}
ACHIEVEMENTS = {
    'first_steps': 'Первые шаги', 'recycler_adept': 'Сортировщик-любитель',
    'paper_master': 'Магистр макулатуры', 'plastic_lord': 'Повелитель пластика',
    'eco_erudite': 'Эко-Эрудит', 'marathoner': 'Марафонец',
    'mentor': 'Наставник', 'perfectionist': 'Перфекционист',
}
BTN_RECYCLED = 'я сдал вторсырье! ✅'; BTN_FIND_POINT = 'найти пункт ♻️'; BTN_PROFILE = 'мой профиль 👤';
BTN_QUIZ = 'эко-викторина 🧠'; BTN_CHALLENGE = 'эко-челлендж 💪'; BTN_LEADERBOARD = 'лидеры 🏆';
BTN_TIP = 'совет дня 💡'; BTN_INVITE = 'пригласить друга 🤝'; BTN_QUESTION = 'задать вопрос 🧠';

# ... (остальные глобальные переменные без изменений) ...
STOP_WORDS = set(['и', 'в', 'во', 'не', 'что', 'он', 'на', 'я', 'с', 'со', 'как', 'а', 'то', 'все', 'она', 'так', 'его', 'но', 'да', 'ты', 'к', 'у', 'же', 'вы', 'за', 'бы', 'по', 'только', 'ее', 'мне', 'было', 'вот', 'от', 'меня', 'еще', 'нет', 'о', 'из', 'ему', 'теперь', 'когда', 'даже', 'ну', 'вдруг', 'ли', 'если', 'уже', 'или', 'ни', 'быть', 'был', 'него', 'до', 'вас', 'нибудь', 'опять', 'уж', 'вам', 'ведь', 'там', 'потом', 'себя', 'ничего', 'ей', 'может', 'они', 'тут', 'где', 'есть', 'надо', 'ней', 'для', 'мы', 'тебя', 'их', 'чем', 'была', 'сам', 'чтоб', 'без', 'будто', 'чего', 'раз', 'тоже', 'себе', 'под', 'будет', 'ж', 'тогда', 'кто', 'этот', 'того', 'потому', 'этого', 'какой', 'совсем', 'ним', 'здесь', 'этом', 'один', 'почти', 'мой', 'тем', 'чтобы', 'нее', 'сейчас', 'были', 'куда', 'зачем', 'всех', 'никогда', 'можно', 'при', 'наконец', 'два', 'об', 'другой', 'хоть', 'после', 'над', 'больше', 'тот', 'через', 'эти', 'нас', 'про', 'всего', 'них', 'какая', 'много', 'разве', 'три', 'эту', 'моя', 'впрочем', 'хорошо', 'свою', 'этой', 'перед', 'иногда', 'лучше', 'чуть', 'том', 'нельзя', 'такой', 'им', 'более', 'всегда', 'конечно', 'всю', 'между', 'такое', 'это'])
SEARCH_TRIGGERS = ['куда сдать', 'где принимают', 'пункты приема', 'пункты приёма', 'адреса', 'адрес', 'найди', 'найти', 'где', 'куда']
JUNK_WORDS = ['а', 'в', 'и', 'с', 'к', 'по']
VAGUE_REPLIES = {'да', 'нет', 'ок', 'хорошо', 'привет', 'спасибо', 'понятно', 'экология', 'пункты сдачи'}

# --- КОНФИГУРАЦИЯ ---
try:
    from config import (TELEGRAM_TOKEN, GIGACHAT_API_KEY, KNOLEDGE_BASE_PATH, 
                        RECYCLING_POINTS_PATH, INTERESTING_FACTS_PATH, 
                        ECO_TIPS_PATH, FALLBACK_POINTS)
except ImportError:
    logging.critical("Ошибка: не удалось найти файл config.py.")
    exit()

MAX_POINTS_TO_SHOW = 3

# --- ИНИЦИАЛИЗАЦИЯ ---
bot = telebot.TeleBot(TELEGRAM_TOKEN)
bot.current_polls = {}
try:
    giga = GigaChatSyncClient(credentials=GIGACHAT_API_KEY, scope='GIGACHAT_API_B2B', verify_ssl_certs=False)
    logging.info("GigaChat успешно инициализирован.")
except Exception as e: 
    logging.error(f"Не удалось инициализировать GigaChat: {e}")
    giga = None

db.init_db()

def load_data():
    points, knowledge, facts, tips = pd.DataFrame(), [], [], []
    try: 
        column_names = ['name', 'city', 'address', 'accepts', 'work_hours', 'phone_number', 'website']
        points = pd.read_csv(RECYCLING_POINTS_PATH, header=0, names=column_names)
        points = points.fillna('') 
        logging.info("✅ recycling_points.csv загружен.")
    except Exception as e: logging.error(f"❌ Ошибка загрузки recycling_points.csv: {e}")
    try:
        with open(KNOLEDGE_BASE_PATH, 'r', encoding='utf-8') as f: knowledge = json.load(f)
        logging.info("✅ knowledge_base.json загружен.")
    except Exception as e: logging.error(f"❌ Ошибка загрузки knowledge_base.json: {e}")
    try:
        with open(INTERESTING_FACTS_PATH, 'r', encoding='utf-8') as f: facts = json.load(f)
        logging.info("✅ interesting_facts.json загружен.")
    except Exception as e: logging.error(f"❌ Ошибка загрузки interesting_facts.json: {e}")
    try:
        with open(ECO_TIPS_PATH, 'r', encoding='utf-8') as f: tips = json.load(f)
        logging.info("✅ eco_tips.json загружен.")
    except Exception as e: logging.error(f"❌ Ошибка загрузки eco_tips.json: {e}")
    return points, knowledge, facts, tips


# --- ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ---
def escape_markdown(text: str) -> str:
    return re.sub(f'([{re.escape(r"_*[]()~`>#+-=|{}.!")}])', r'\\\1', text)

def send_message_safely(message, text_to_send, **kwargs):
    """
    Пытается ответить на сообщение с MarkdownV2. 
    При ошибке парсинга, отправляет как простой текст.
    По умолчанию добавляет основную клавиатуру.
    """
    # Если в kwargs явно не передана другая клавиатура (или ее удаление),
    # то мы добавляем нашу основную клавиатуру по умолчанию.
    if 'reply_markup' not in kwargs:
        kwargs['reply_markup'] = create_main_keyboard()

    try:
        # Устанавливаем parse_mode по умолчанию, если он не передан
        if 'parse_mode' not in kwargs:
            kwargs['parse_mode'] = 'MarkdownV2'
        bot.reply_to(message, text_to_send, **kwargs)

    except telebot.apihelper.ApiTelegramException as e:
        if "can't parse entities" in str(e):
            logging.warning(f"MarkdownV2 parsing failed for chat {message.chat.id}. Sending as plain text.")
            kwargs.pop('parse_mode', None)
            bot.reply_to(message, text_to_send, **kwargs)
        else:
            logging.error(f"Failed to send message to {message.chat.id}: {e}")

def create_main_keyboard():
    markup = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    markup.add(types.KeyboardButton(BTN_RECYCLED), types.KeyboardButton(BTN_FIND_POINT))
    markup.add(types.KeyboardButton(BTN_PROFILE), types.KeyboardButton(BTN_QUIZ))
    markup.add(types.KeyboardButton(BTN_CHALLENGE), types.KeyboardButton(BTN_LEADERBOARD))
    markup.add(types.KeyboardButton(BTN_TIP), types.KeyboardButton(BTN_INVITE))
    markup.add(types.KeyboardButton(BTN_QUESTION))
    return markup
    
# --- ФУНКЦИИ ГЕЙМИФИКАЦИИ ---
def add_points_and_notify(user_id: int, points: int, reason_message: str, check_referral=False):
    profile_before = db.get_or_create_user_profile(user_id)
    db.add_points(user_id, points)
    
    notification_text = f"{escape_markdown(reason_message)}\n\nВы получили *{points} Эко-Очков*\\!"
    try:
        bot.send_message(user_id, notification_text, parse_mode='MarkdownV2')
    except telebot.apihelper.ApiTelegramException as e:
        if "can't parse entities" in str(e):
            logging.warning(f"MarkdownV2 parsing failed for notification to {user_id}. Sending as plain text.")
            bot.send_message(user_id, notification_text.replace("*", "").replace("\\", ""))
        else:
            logging.error(f"Не удалось отправить уведомление о начислении очков пользователю {user_id}: {e}")

    profile_after = db.get_or_create_user_profile(user_id)
    check_for_level_up(user_id, profile_after['total_points'], profile_after['level'])
    check_for_achievements(user_id)

    if check_referral:
        check_referral_bonus(user_id, profile_before, profile_after)

def check_referral_bonus(user_id, profile_before, profile_after):
    referrer_id = profile_after.get('referred_by')
    bonus_was_given = profile_after.get('referrer_bonus_given', 0) == 1

    if referrer_id and not bonus_was_given and profile_before['total_points'] < 50 and profile_after['total_points'] >= 50:
        logging.info(f"User {user_id} crossed 50 points. Awarding bonus to referrer {referrer_id}.")
        user_name = "Ваш друг"
        try:
            user_info = bot.get_chat(user_id)
            user_name = user_info.first_name or user_info.username
        except Exception as e:
            logging.error(f"Could not get user info for {user_id}: {e}")
        
        add_points_and_notify(referrer_id, POINTS_FOR_INVITE, f"Ваш друг {user_name} набрал первые 50 очков!", check_referral=False)
        
        referrer_profile = db.get_or_create_user_profile(referrer_id)
        new_referrals_count = referrer_profile.get('referrals_count', 0) + 1
        db.update_profile_stats(referrer_id, {'referrals_count': new_referrals_count})
        db.update_profile_stats(user_id, {'referrer_bonus_given': 1})

def check_for_level_up(user_id, user_points, user_level):
    new_level_num = user_level
    for level_num, level_info in sorted(LEVELS.items(), reverse=True):
        if user_points >= level_info["min_points"]:
            new_level_num = level_num
            break
    
    if new_level_num > user_level:
        db.update_profile_stats(user_id, {'level': new_level_num})
        level_name = LEVELS[new_level_num]["name"]
        bot.send_message(user_id, f"🎉 *НОВЫЙ УРОВЕНЬ* 🎉\n\nВы стали *{escape_markdown(level_name)}*\\! Так держать\\!", parse_mode='MarkdownV2')

def check_for_achievements(user_id):
    profile = db.get_or_create_user_profile(user_id)
    user_achievements = db.get_user_achievements(user_id)
    def grant_if_new(ach_id):
        if ach_id not in user_achievements:
            db.grant_achievement(user_id, ach_id)
            add_points_and_notify(user_id, POINTS_FOR_ACHIEVEMENT, f"Новое достижение: {ACHIEVEMENTS[ach_id]}!", check_referral=False)
    if profile['total_points'] >= 10: grant_if_new('first_steps')
    if profile['recycle_report_count'] >= 10: grant_if_new('recycler_adept')
    if profile['quiz_correct_streak'] >= 10: grant_if_new('eco_erudite')
    if profile['challenges_completed_count'] >= 3: grant_if_new('marathoner')
    if profile['referrals_count'] >= 1: grant_if_new('mentor')
    if profile['recycle_streak_count'] >= 7: grant_if_new('perfectionist')
    
def extract_entities(text: str) -> Tuple[str | None, str | None, str | None]:
    clean_text = re.sub(r'[^\w\s]', '', text).lower()
    city, material, district = None, None, None
    
    # Обновленная логика поиска города с fuzzy matching
    city_map = {'курган': ['курган', 'кгн']}
    all_city_aliases = [alias for sublist in city_map.values() for alias in sublist]
    
    # Находим наиболее похожее название города в тексте
    best_match = process.extractOne(clean_text, all_city_aliases, score_cutoff=80) # Порог 80% схожести
    
    if best_match:
        matched_alias = best_match[0]
        # Находим полное имя города по найденному алиасу
        for full_city_name, aliases in city_map.items():
            if matched_alias in aliases:
                city = full_city_name
                # Удаляем все варианты названия города из текста, чтобы не мешали поиску материала
                for alias_to_remove in aliases:
                    clean_text = clean_text.replace(alias_to_remove, '')
                break

    temp_material = clean_text
    for trigger in SEARCH_TRIGGERS: temp_material = temp_material.replace(trigger, '')
    words = temp_material.strip().split()
    while words and words[0] in JUNK_WORDS: words.pop(0)
    while words and words[-1] in JUNK_WORDS: words.pop(-1)
    material = ' '.join(words)
    
    # Добавим проверку, чтобы не возвращать пустой материал, если был найден только город
    if not material.strip():
        material = None
        
    return material, city, district

def find_recycling_points(material: str, city: str) -> Tuple[List[dict], List[str]]:
    if points_df.empty or not material or not city: return [], []
    try:
        synonym_map = {'шины': ['шин', 'покрышк', 'колес'], 'футболки': ['футболк', 'одежд', 'вещи', 'текстиль'],'бутылки': ['бутылк', 'пэт', 'пластик'], 'пластик': ['пластик', 'пэт', 'бутылк', 'hdpe', 'пнд'], 'батарейки': ['батарейк', 'аккумулятор'], 'бумага': ['бумаг', 'макулатур', 'картон', 'книг'], 'стекло': ['стекл', 'банк', 'стеклотар'], 'одежда': ['одежд', 'вещи', 'текстиль', 'футболк'], 'металл': ['металл', 'жестян', 'алюмин', 'чермет', 'цветмет'], 'крышки': ['крышк'], 'техника': ['техник', 'электроника'], 'опасные отходы': ['опасные отходы', 'ртуть', 'градусник', 'лампочк', 'лампа'], 'зубные щетки': ['зубная щетка', 'зубные щетки']}
        for key, values in synonym_map.items():
            if any(val in material for val in values): search_terms = values; break
        if not search_terms: search_terms = [material]
        city_points = points_df[points_df['city'].str.lower() == city.lower()]
        valid_points = city_points.dropna(subset=['accepts'])
        pattern = '|'.join(search_terms)
        found_points = valid_points[valid_points['accepts'].str.lower().str.contains(pattern, case=False, na=False)]
        return found_points.to_dict('records'), search_terms
    except Exception as e: print(f"Ошибка поиска: {e}"); return [], []

def format_points_response(points: List[dict], header: str) -> str:
    response_parts = [header]
    for idx, point in enumerate(points, 1):
        name = escape_markdown(str(point.get('name', 'Без названия')))
        address = escape_markdown(str(point.get('address', 'Адрес не указан')))
        
        work_hours_value = str(point.get('work_hours', ''))
        work_hours_text = work_hours_value if work_hours_value else 'Время работы не указано'
        work_hours = escape_markdown(work_hours_text)
        
        response_parts.append(f"📍 *{idx}\\. {name}*\n   *Адрес:* {address}\n   *Время работы:* {work_hours}")
    return "\n\n".join(response_parts)

def get_knowledge_answer(question: str) -> Tuple[str, str | None]:
    clean_question = re.sub(r'[^\w\s]', '', question.lower())
    user_words = set(clean_question.split()) - STOP_WORDS
    if not user_words: return "", None
    best_match_score = 0
    best_answer, best_context = "", None
    for item in knowledge_base:
        kb_clean_question = re.sub(r'[^\w\s]', '', item['question'].lower())
        kb_words = set(kb_clean_question.split()) - STOP_WORDS
        if not kb_words: continue
        score = len(user_words.intersection(kb_words))
        ratio = score / len(kb_words) if len(kb_words) > 0 else 0
        if score >= 2 and ratio > 0.6 and score > best_match_score:
            best_match_score, best_answer = score, item['answer']
            best_context = item.get('context_keyword')
    return (best_answer, best_context) if best_match_score >= 2 else ("", None)
    
def get_user_intent(question: str) -> str:
    if not giga: return "GENERAL"
    system_prompt = ("Твоя задача - определить намерение пользователя. Ответь ОДНИМ словом. "
                     "1. Если пользователь хочет найти место, куда что-то сдать, или спрашивает адрес - ответь SEARCH. "
                     "2. Если он спрашивает о твоих возможностях, просит помощи ('помоги', 'что ты умеешь') или здоровается - ответь HELP. "
                     "3. Если речь о челленджах, вызовах, заданиях - ответь CHALLENGE. "
                     "4. Во всех остальных случаях (общие вопросы об экологии) - ответь GENERAL.")
    payload = Chat(messages=[Messages(role=MessagesRole.SYSTEM, content=system_prompt), Messages(role=MessagesRole.USER, content=question)], temperature=0.1, model='GigaChat-Max')
    try:
        response = giga.chat(payload)
        intent = response.choices[0].message.content.strip().upper()
        if intent in ["SEARCH", "HELP", "CHALLENGE", "GENERAL"]:
            logging.info(f"Intent for '{question[:30]}...' -> {intent}")
            return intent
        else:
            logging.warning(f"Unexpected intent response: '{intent}'. Defaulting to GENERAL.")
            return "GENERAL"
    except Exception as e:
        logging.error(f"Error in get_user_intent: {e}")
        return "GENERAL"

def get_gigachat_answer(question: str, history: deque) -> str:
    if not giga: return "Извините, модуль GigaChat не был загружен."
    system_prompt = (
        "Твоя роль - дружелюбный и полезный эксперт по экологии. Ты помнишь предыдущие сообщения "
        "и можешь поддерживать осмысленный диалог. Отвечай на вопросы, связанные с экологией и переработкой. "
        "Будь кратким, но информативным. Отвечай строго на русском языке. Не включай в ответ примеры вопросов или текст на других языках. "
        "Важно: Не приводи в пример названия реальных компаний, брендов или имена людей, если тебя об этом не просят напрямую. "
        "Если вопрос не по теме, вежливо откажи: 'К сожалению, я могу обсуждать только вопросы, связанные с экологией.'"
    )
    messages_for_giga = [Messages(role=MessagesRole.SYSTEM, content=system_prompt)]
    for msg in history:
        role = MessagesRole.USER if msg['role'] == 'user' else MessagesRole.ASSISTANT
        messages_for_giga.append(Messages(role=role, content=msg['content']))
    messages_for_giga.append(Messages(role=MessagesRole.USER, content=question))
    payload = Chat(messages=messages_for_giga, temperature=0.7, model='GigaChat-Max')
    try:
        return giga.chat(payload).choices[0].message.content
    except Exception as e:
        logging.error(f"Ошибка при обращении к GigaChat: {e}")
        return "Извините, произошла ошибка."

def handle_info_request(text: str) -> str | None:
    text_lower = text.lower()
    for city, point_info in FALLBACK_POINTS.items():
        if point_info['name'].lower() in text_lower:
            if 'телефон' in text_lower or 'номер' in text_lower: return f"📞 Телефон пункта '{point_info['name']}': `{escape_markdown(point_info.get('phone', 'не указан'))}`"
            if 'сайт' in text_lower: return f"🌐 Сайт пункта '{point_info['name']}': {escape_markdown(point_info.get('website', 'не указан'))}"
            if 'адрес' in text_lower: return f"📍 Адрес пункта '{point_info['name']}': {escape_markdown(point_info.get('address', 'не указан'))}"
    return None
    
def check_challenges():
    logging.info("Запущена проверка челленджей...")
    active_challenges = db.get_all_active_challenges()
    for challenge in active_challenges:
        user_id, challenge_id = challenge['user_id'], challenge['challenge_id']
        start_date = date.fromisoformat(challenge['start_date'])
        challenge_info = challenges.CHALLENGES[challenge_id]
        days_passed = (date.today() - start_date).days
        if days_passed >= challenge_info['duration_days']:
            db.end_challenge(user_id)
            profile = db.get_or_create_user_profile(user_id)
            new_count = profile['challenges_completed_count'] + 1
            db.update_profile_stats(user_id, {'challenges_completed_count': new_count})
            add_points_and_notify(user_id, POINTS_FOR_CHALLENGE, f"За завершение челленджа «{challenge_info['title']}»", check_referral=True)
            bot.send_message(user_id, challenge_info['end_message'])
            logging.info(f"Челлендж {challenge_id} завершен для {user_id}.")
        elif days_passed > 0 and (days_passed + 1) % 2 == 0 : # Напоминание раз в 2 дня
            bot.send_message(user_id, f"День {days_passed + 1}: {challenge_info['daily_message']}")
            logging.info(f"Отправлено напоминание по челленджу для {user_id}")

def send_daily_tip():
    logging.info("Запущена рассылка эко-советов...")
    subscribers = db.get_all_subscribers()
    if not subscribers or not eco_tips: 
        logging.info("Нет подписчиков или советов для рассылки.")
        return
    tip_of_the_day = random.choice(eco_tips)
    message = f"💡 *Эко-совет дня:*\n\n{escape_markdown(tip_of_the_day)}"
    for user_id in subscribers:
        try: bot.send_message(user_id, message, parse_mode='MarkdownV2')
        except Exception as e:
            if 'bot was blocked' in str(e): 
                logging.warning(f"{user_id} заблокировал бота. Удаляем из подписчиков.")
                db.remove_subscriber(user_id)
            else: logging.error(f"Ошибка отправки совета {user_id}: {e}")
    logging.info(f"Рассылка советов завершена для {len(subscribers)} пользователей.")

def show_all_challenges(chat_id, edit_message_id=None):
    markup = types.InlineKeyboardMarkup()
    for c_id, c_info in challenges.CHALLENGES.items():
        markup.add(types.InlineKeyboardButton(c_info['title'], callback_data=f"show_challenge_{c_id}"))
    text = "Выберите челлендж:"
    try:
        if edit_message_id:
            bot.edit_message_text(text, chat_id, edit_message_id, reply_markup=markup)
        else:
            bot.send_message(chat_id, text, reply_markup=markup)
    except Exception as e:
        print(f"Ошибка в show_all_challenges: {e}")

def generate_quiz_data():
    if not giga or not (interesting_facts and eco_tips):
        return None
    all_facts = [fact for fact in (interesting_facts + eco_tips) if len(fact) <= 80]
    if len(all_facts) < 1: return None
    base_fact = random.choice(all_facts)
    prompt = (
        f"Создай вопрос для викторины на основе этого факта: '{base_fact}'.\n"
        "Затем придумай 3 неверных, но правдоподобных ответа на этот вопрос.\n"
        "Верни результат в формате:\n"
        "Вопрос: [Твой вопрос здесь]\n"
        "Верный ответ: [Перефразированный факт или краткий ответ на вопрос]\n"
        "Неверный ответ 1: [Твой первый неверный вариант]\n"
        "Неверный ответ 2: [Твой второй неверный вариант]\n"
        "Неверный ответ 3: [Твой третий неверный вариант]\n"
        "Каждый вариант ответа не должен превышать 80 символов."
    )
    payload = Chat(messages=[Messages(role=MessagesRole.USER, content=prompt)], temperature=0.7, model='GigaChat-Max')
    try:
        response_text = giga.chat(payload).choices[0].message.content
        lines = response_text.strip().split('\n')
        quiz_dict = {}
        for line in lines:
            if ':' in line:
                key, value = line.split(':', 1)
                quiz_dict[key.strip()] = value.strip()
        question = quiz_dict.get("Вопрос")
        correct_answer = quiz_dict.get("Верный ответ")
        wrong_answers = [
            quiz_dict.get("Неверный ответ 1"),
            quiz_dict.get("Неверный ответ 2"),
            quiz_dict.get("Неверный ответ 3")
        ]
        if not all([question, correct_answer] + wrong_answers):
            logging.error("GigaChat returned malformed quiz data.")
            return None
        options = [correct_answer] + wrong_answers
        random.shuffle(options)
        correct_option_id = options.index(correct_answer)
        return {"question": question, "options": options, "correct_option_id": correct_option_id}
    except Exception as e:
        logging.error(f"Failed to generate quiz data with GigaChat: {e}")
        return None

# Вставьте этот код в bot_polling.py

def send_help_message(message):
    """Отправляет пользователю подробную инструкцию по использованию бота."""
    
    help_text = """
*Краткая инструкция: Как пользоваться Эко\\-Помощником* ♻️

Привет\\! Я ваш личный гид в мире экологии и переработки\\. Моя цель — помочь вам сделать полезные привычки простыми и интересными\\. Вместе мы сможем сделать нашу планету чище\\!

*Что я умею?*

📍 *Находить пункты приема вторсырья*
Просто напишите мне, что и где вы хотите сдать\\. Я пойму даже с опечатками\\!
Примеры:
`Куда сдать батарейки?`
`Стекло в Кургане`


🧠 *Отвечать на вопросы об экологии*
Спрашивайте что угодно о переработке, сортировке или экологичном образе жизни\\.
Примеры:
`Как подготовить пластик к сдаче?`
`Почему нельзя выбрасывать лампочки?`
`Что такое zero waste?`

💪 *Предлагать Эко\\-Челленджи*
Хотите выработать полезную привычку? Нажмите кнопку *«Эко\\-челлендж 💪»* и выберите задание на несколько дней\\. За выполнение — особые награды\\!

💡 *Давать полезные советы и факты*
Нажмите *«Совет дня 💡»*, чтобы узнать что\\-то новое, или *«Эко\\-викторина 🧠»*, чтобы проверить свои знания и заработать очки\\!

✨ *Ваша Эко\\-Активность: Как заработать баллы?*

За каждое полезное действие вы получаете *Эко\\-Очки*\\. Они повышают ваш уровень, открывают достижения и помогают соревноваться с другими в *Таблице Лидеров 🏆*\\!

Вот за что начисляются баллы:
• *\\+75 очков* — за успешное завершение *Эко\\-Челленджа*\\.
• *\\+30 очков* — за каждого *приглашенного друга* \\(кнопка «Пригласить друга 🤝»\\)\\.
• *\\+20 очков* — за получение нового *достижения*\\.
• *\\+10 очков* — за *ежедневный отчет* о сдаче вторсырья \\(кнопка «Я сдал вторсырье\\! ✅»\\)\\.
• *\\+5 очков* — за каждый *правильный ответ* в Эко\\-Викторине\\.
• *\\+1 очко* — за получение *«Совета дня»*\\.

Ваш прогресс всегда можно посмотреть, нажав кнопку *«Мой профиль 👤»*\\.

*Готовы начать? Просто задайте свой первый вопрос или воспользуйтесь кнопками меню\\! Ваш вклад очень важен\\!*
"""
    send_message_safely(message, help_text)

# --- ОБРАБОТЧИКИ TELEGRAM ---
@bot.message_handler(commands=['start'])
def send_welcome(message):
    user_id = message.from_user.id
    args = message.text.split()
    referred_by = None
    
    if len(args) > 1 and args[1].startswith('ref_'):
        try:
            referred_by = int(args[1].replace('ref_', ''))
            if referred_by == user_id: referred_by = None
        except (ValueError, IndexError):
            referred_by = None

    db.get_or_create_user_profile(user_id, referred_by=referred_by)
    if referred_by:
        bot.send_message(referred_by, "🎉 Ваш друг присоединился по вашей ссылке! Вы получите бонус, как только он наберет 50 очков.")
    
    bot.reply_to(message, "♻️ *Привет\\! Я ваш эко\\-помощник\\.*\n\nЧтобы узнать обо всех возможностях, отправьте команду /help или просто напишите «помощь»\\.\n\nИспользуйте кнопки меню ниже или задайте свой вопрос\\!", parse_mode='MarkdownV2', reply_markup=create_main_keyboard())

@bot.message_handler(commands=['recycled'])
def handle_recycled(message):
    user_id = message.from_user.id
    profile = db.get_or_create_user_profile(user_id)
    today = date.today()
    today_str = today.isoformat()

    if profile.get('last_recycle_report_date') == today_str:
        bot.reply_to(message, "Вы уже сообщали о сдаче вторсырья сегодня. Спасибо! 😉")
        return

    yesterday_str = (today - timedelta(days=1)).isoformat()
    current_streak = profile['recycle_streak_count']
    current_streak = current_streak + 1 if profile.get('last_recycle_report_date') == yesterday_str else 1
    
    db.update_profile_stats(user_id, {
        'recycle_report_count': profile['recycle_report_count'] + 1,
        'last_recycle_report_date': today_str,
        'recycle_streak_count': current_streak
    })
    
    add_points_and_notify(user_id, POINTS_FOR_RECYCLE, "За ежедневный отчет о сдаче вторсырья", check_referral=True)
    
    if current_streak >= 5 and current_streak % 7 == 5:
         add_points_and_notify(user_id, POINTS_FOR_STREAK, f"За {current_streak}-дневную серию сдачи вторсырья!", check_referral=True)

@bot.message_handler(commands=['profile'])
def handle_profile(message):
    user_id = message.from_user.id
    profile = db.get_or_create_user_profile(user_id)
    achievements = db.get_user_achievements(user_id)
    
    level_num = profile.get('level', 1)
    level_info = LEVELS[level_num]
    
    points_needed_str = "МАКСИМУМ"
    next_level_num = level_num + 1
    if next_level_num in LEVELS:
        points_needed = LEVELS[next_level_num]['min_points'] - profile['total_points']
        points_needed_str = str(points_needed) if points_needed > 0 else "0"

    response_parts = [
        f"👤 *Ваш Эко\\-Профиль*",
        f"🏆 *Уровень:* {level_num} \\- *{escape_markdown(level_info['name'])}*",
        f"✨ *Всего очков:* {profile['total_points']}",
        f"🌿 *Очки в этом квартале:* {profile['quarterly_points']}",
        f"🎯 *До следующего уровня:* {points_needed_str} очков"
    ]

    if achievements:
        response_parts.append("\n🏅 *Ваши достижения:*")
        for ach_id in achievements:
            response_parts.append(f"\\- {escape_markdown(ACHIEVEMENTS.get(ach_id, ach_id))}")

    send_message_safely(message, "\n".join(response_parts))

@bot.message_handler(commands=['leaderboard'])
def handle_leaderboard(message):
    leaders = db.get_leaderboard()
    if not leaders:
        send_message_safely(message, "Пока что у нас нет лидеров в этом квартале. Станьте первым!")
        return

    response_parts = ["🏆 *Таблица Лидеров (текущий квартал)* 🏆\n"]
    medals = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣"]
    
    for i, leader in enumerate(leaders):
        try:
            user_info = bot.get_chat(leader['user_id'])
            user_name = user_info.first_name or user_info.username or f"Герой"
        except Exception: user_name = f"Герой"
        response_parts.append(f"{medals[i]} *{escape_markdown(user_name)}* \\- {leader['quarterly_points']} очков")

    send_message_safely(message, "\n".join(response_parts))

@bot.message_handler(commands=['help'])
def handle_help_command(message):
    """Обрабатывает команду /help и вызывает функцию с инструкцией."""
    send_help_message(message)

@bot.message_handler(commands=['quiz'])
def handle_quiz(message):
    user_id = message.from_user.id
    profile = db.get_or_create_user_profile(user_id)
    today_str = date.today().isoformat()

    if profile.get('last_quiz_date') == today_str:
        bot.reply_to(message, "Вы уже отвечали на викторину сегодня. Новый вопрос будет завтра!")
        return
        
    db.update_profile_stats(user_id, {'last_quiz_date': today_str})
    
    bot.send_message(message.chat.id, "🧠 Генерирую для вас уникальный вопрос... Пожалуйста, подождите немного.")
    quiz_data = generate_quiz_data()
    
    if not quiz_data:
        bot.reply_to(message, "Не удалось создать вопрос для викторины. Попробуйте, пожалуйста, позже.")
        db.update_profile_stats(user_id, {'last_quiz_date': None})
        return

    poll_message = bot.send_poll(
        chat_id=message.chat.id,
        question=quiz_data["question"],
        options=quiz_data["options"],
        type='quiz',
        correct_option_id=quiz_data["correct_option_id"],
        is_anonymous=False
    )
    
    bot.current_polls[poll_message.poll.id] = quiz_data["correct_option_id"]

@bot.poll_answer_handler()
def handle_poll_answer(poll_answer):
    user_id = poll_answer.user.id
    
    correct_option_id = bot.current_polls.pop(poll_answer.poll_id, None)
    
    if correct_option_id is None:
        logging.warning(f"Poll with ID {poll_answer.poll_id} not found in memory.")
        return

    profile = db.get_or_create_user_profile(user_id)
    
    if correct_option_id == poll_answer.option_ids[0]:
        new_streak = profile['quiz_correct_streak'] + 1
        db.update_profile_stats(user_id, {'quiz_correct_streak': new_streak})
        add_points_and_notify(user_id, POINTS_FOR_QUIZ, "За правильный ответ в викторине", check_referral=True)
    else:
        db.update_profile_stats(user_id, {'quiz_correct_streak': 0})
        bot.send_message(user_id, "В этот раз неверно, но не переживайте! В следующий раз обязательно получится. 👍")

@bot.message_handler(commands=['invite'])
def handle_invite(message):
    user_id = message.from_user.id
    bot_info = bot.get_me()
    bot_username = bot_info.username
    invite_link = f"https://t.me/{bot_username}?start=ref_{user_id}"
    
    response = (f"🤝 *Пригласите друга и получите бонус\\!* \n\n"
                f"Отправьте вашему другу эту специальную ссылку\\. Когда он присоединится и наберет свои первые 50 очков, вы получите *{POINTS_FOR_INVITE} Эко-Очков*\\!\n\n"
                f"Ваша ссылка:\n`{invite_link}`")
    
    bot.send_message(user_id, response, parse_mode='Markdown')

@bot.message_handler(func=lambda message: True)
def handle_text(message):
    try:
        # --- 1. Начальная настройка ---
        user_id = message.from_user.id
        text = message.text.strip()
        text_lower = text.lower()
        db.get_or_create_user_profile(user_id)

        # Проверка на ключевые слова для вызова инструкции
        HELP_TRIGGERS = {'помощь', 'помоги', 'инструкция', 'что ты умеешь', 'хелп', 'справка'}
        if text_lower in HELP_TRIGGERS:
            send_help_message(message)
            return # Завершаем выполнение, чтобы не идти дальше

        # Инициализация контекста для диалога
        if user_id not in user_context:
            user_context[user_id] = {'history': deque(maxlen=MAX_HISTORY_LENGTH)}

        # --- 2. Обработка точных нажатий на кнопки меню ---
        button_handlers = {
            BTN_RECYCLED.lower(): handle_recycled,
            BTN_PROFILE.lower(): handle_profile,
            BTN_LEADERBOARD.lower(): handle_leaderboard,
            BTN_QUIZ.lower(): handle_quiz,
            BTN_INVITE.lower(): handle_invite
        }
        if text_lower in button_handlers:
            button_handlers[text_lower](message)
            return

        # --- 3.  Приоритетная обработка явных поисковых запросов ---
        # Пытаемся извлечь материал и город. Если успешно, это точно поиск.
        potential_material, potential_city, potential_district = extract_entities(text_lower)
        
        if potential_city and potential_material:
            logging.info(f"Обнаружен прямой поисковый запрос: Город={potential_city}, Материал={potential_material}")
            
            bot.send_chat_action(message.chat.id, 'typing')
            all_city_points, search_terms = find_recycling_points(potential_material, potential_city)

            if not all_city_points:
                fallback_point = FALLBACK_POINTS.get(potential_city.lower())
                if fallback_point:
                    city_in_case = "Кургане"
                    response = (f"😔 К сожалению, я не нашел специализированных пунктов.\n\n"
                             f"Но в городе Кургане есть универсальный вариант:\n\n"
                             f"📍 {escape_markdown(fallback_point['name'])}\n"
                             f"   Адрес: {fallback_point['address']}\n"  # <-- Убрали escape_markdown
                             f"   Телефон: {fallback_point.get('phone', 'не указан')}\n\n"
                             f"⚠️ Важно: {fallback_point['note']}") # <-- Убрали escape_markdown
                else:
                    # Эта часть сработает, только если в config.py вообще нет записи для этого города.
                    response = f"К сожалению, я не нашел пунктов приема для *'{escape_markdown(potential_material)}'* в городе *{escape_markdown(potential_city.capitalize())}*\\."
                send_message_safely(message, response)
            else:
                if potential_district:
                    points_in_district = [p for p in all_city_points if potential_district in p.get('address', '').lower()]
                    if points_in_district:
                        all_city_points = points_in_district

                unique_points_by_name = {f"{p.get('name', '')}:{p.get('address', '')}".lower(): p for p in all_city_points}
                unique_points_list = list(unique_points_by_name.values())

                user_context[user_id].update({'found_points': unique_points_list, 'page': 0, 'city': potential_city, 'district': potential_district})
                points_to_show = unique_points_list[:MAX_POINTS_TO_SHOW]
                header = f"✅ *Вот что удалось найти в городе {escape_markdown(potential_city.capitalize())}:*"
                if potential_district and any(potential_district in p.get('address', '').lower() for p in points_to_show):
                     header = f"✅ *Вот что удалось найти в районе {escape_markdown(potential_district.capitalize())}:*"

                response = format_points_response(points_to_show, header)
                markup = types.InlineKeyboardMarkup()
                if len(unique_points_list) > MAX_POINTS_TO_SHOW:
                    markup.add(types.InlineKeyboardButton("🔄 Показать другие варианты", callback_data=f"more_points_{random.randint(1,1000)}"))
                send_message_safely(message, response, reply_markup=markup)

            return

        # --- 4. Обработка остальных кнопок и команд-триггеров ---
        if text_lower == BTN_CHALLENGE.lower():
            current_challenge = db.get_user_challenge(user_id)
            if current_challenge:
                challenge_info = challenges.CHALLENGES[current_challenge['challenge_id']]
                start_date = date.fromisoformat(current_challenge['start_date'])
                days_passed = (date.today() - start_date).days
                response = (f"Вы уже участвуете в челлендже:\n\n*{challenge_info['title']}*\nДень {days_passed + 1} из {challenge_info['duration_days']}.\n\nХотите отказаться и выбрать новый?")
                markup = types.InlineKeyboardMarkup()
                markup.add(types.InlineKeyboardButton("Отказаться и выбрать новый", callback_data="show_all_challenges"), types.InlineKeyboardButton("Нет, я продолжаю!", callback_data="cancel_action"))
                bot.send_message(message.chat.id, response, parse_mode='Markdown', reply_markup=markup)
            else:
                show_all_challenges(message.chat.id)
            return

        if text_lower == BTN_TIP.lower():
            tip_of_the_day = random.choice(eco_tips) if eco_tips else "Извините, у меня закончились советы."
            response = f"💡 *Случайный совет:*\n\n{escape_markdown(tip_of_the_day)}"
            profile = db.get_or_create_user_profile(user_id)
            today_str = date.today().isoformat()
            if profile.get('last_tip_date') != today_str:
                db.update_profile_stats(user_id, {'last_tip_date': today_str})
                add_points_and_notify(user_id, POINTS_FOR_TIP, "За проявленный интерес к экологии", check_referral=True)
            send_message_safely(message, response)
            return

        if text_lower.startswith(BTN_FIND_POINT.split()[0].lower()):
            bot.reply_to(message, "Какой вид вторсырья и в каком городе сдать?\n\nНапример: *Батарейки в Кургане*", parse_mode='Markdown')
            return
        
        if text_lower.startswith(BTN_QUESTION.split()[0].lower()):
            bot.reply_to(message, "Слушаю ваш вопрос о переработке отходов!")
            return

        # --- 5. Поиск ответа в локальной базе знаний ---
        answer, context_to_save = get_knowledge_answer(text_lower)
        if answer:
            response, markup = escape_markdown(answer), None
            if context_to_save:
                user_context[user_id]['last_material'] = context_to_save
                markup = types.InlineKeyboardMarkup()
                markup.add(types.InlineKeyboardButton(f"Найти пункты для '{context_to_save}'", callback_data=f"search_context_{context_to_save}"))
            
            send_message_safely(message, response, reply_markup=markup)
            # Добавляем в историю для поддержания диалога
            user_context[user_id]['history'].append({'role': 'user', 'content': text})
            user_context[user_id]['history'].append({'role': 'assistant', 'content': answer})
            return

        # --- 6. Если ничего не подошло - обращаемся к GigaChat (Fallback) ---
        bot.send_chat_action(message.chat.id, 'typing')

        # Определяем намерение, если предыдущие шаги не дали результата
        intent = get_user_intent(text_lower)
        response = ""

        if intent == "SEARCH":
            material, city, district = extract_entities(text_lower)
            if not city:
                city = "курган"
                logging.info(f"Город не указан, автоматически используется 'курган' для материала: {material}")

            all_city_points, search_terms = find_recycling_points(material, city)
            if not all_city_points:
                
                fallback_point = FALLBACK_POINTS.get(city.lower())
                if fallback_point:
                    response = (f"😔 К сожалению, я не нашел специализированных пунктов.\n\n"
                                f"Но в городе {escape_markdown(city.capitalize())} есть универсальный вариант:\n\n"
                                f"📍 *{escape_markdown(fallback_point['name'])}*\n"
                                f"   *Адрес:* {escape_markdown(fallback_point['address'])}\n"
                                f"   *Телефон:* `{fallback_point.get('phone', 'не указан')}`\n\n"
                                f"⚠️ *Важно:* {escape_markdown(fallback_point['note'])}")
                    
                else:
                    response = f"К сожалению, подходящих пунктов для '{escape_markdown(material)}' не нашлось."
                
                send_message_safely(message, response) # Отправляем сообщение здесь
                return # И завершаем
            else:
                # ... (логика форматирования и отправки, если точки найдены, остается без изменений) ...
                unique_points_by_name = {f"{p.get('name', '')}:{p.get('address', '')}".lower(): p for p in all_city_points}
                unique_points_list = list(unique_points_by_name.values())
                user_context[user_id].update({'found_points': unique_points_list, 'page': 0, 'city': city, 'district': district})
                points_to_show = unique_points_list[:MAX_POINTS_TO_SHOW]
                header = f"✅ Нашел пункты в городе *{escape_markdown(city.capitalize())}*:"
                response = format_points_response(points_to_show, header)
                markup = types.InlineKeyboardMarkup()
                if len(unique_points_list) > MAX_POINTS_TO_SHOW:
                    markup.add(types.InlineKeyboardButton("🔄 Показать другие варианты", callback_data=f"more_points_{random.randint(1,1000)}"))
                send_message_safely(message, response, reply_markup=markup)
                return # Завершаем, так как ответ уже отправлен
            
        elif intent == "HELP":
            send_help_message(message)
            return # Завершаем, так как ответ уже отправлен
        
        elif intent == "CHALLENGE":
            show_all_challenges(user_id)
            return
        else: # GENERAL
            if len(text.split()) <= 2 and text_lower in VAGUE_REPLIES:
                response = "Привет! Кажется, твой ответ неполный. Задай, пожалуйста, полноценный вопрос или воспользуйся кнопками меню."
            else:
                history = user_context[user_id].get('history', deque(maxlen=MAX_HISTORY_LENGTH))
                response_giga = get_gigachat_answer(text, history)
                response = escape_markdown(response_giga)

        # --- 7. Отправка ответа и сохранение истории ---
        if response:
             clean_response_for_history = re.sub(r'\\([_*\[\]()~`>#+\-={}.!])', r'\1', response)
             user_context[user_id]['history'].append({'role': 'user', 'content': text})
             user_context[user_id]['history'].append({'role': 'assistant', 'content': clean_response_for_history})
             send_message_safely(message, response)

    except Exception as e:
        logging.critical(f"Произошла критическая ошибка в handle_text: {e}", exc_info=True)
        bot.reply_to(message, "Ой, что-то пошло не так... Попробуйте переформулировать запрос или воспользуйтесь кнопками меню.")

@bot.callback_query_handler(func=lambda call: True)
def handle_callbacks(call):
    user_id = call.from_user.id
    data = call.data
    try:
        if data.startswith('more_points_'):
            # ... (логика more_points_) ...
            if user_id not in user_context or 'found_points' not in user_context[user_id]:
                bot.answer_callback_query(call.id, text="Данные устарели. Сделайте новый запрос.")
                bot.edit_message_text("Данные для поиска устарели.", call.message.chat.id, call.message.message_id)
                return
            context = user_context[user_id]
            all_points = context['found_points']
            current_page = context.get('page', 0)
            city = context['city']
            district = context.get('district')

            new_page = current_page + 1
            start_index = new_page * MAX_POINTS_TO_SHOW
            if start_index >= len(all_points):
                new_page, start_index = 0, 0
                bot.answer_callback_query(call.id, text="Это все варианты. Показываю с начала.")
            else:
                bot.answer_callback_query(call.id)

            context['page'] = new_page
            points_to_show = all_points[start_index : start_index + MAX_POINTS_TO_SHOW]
            
            header = f"✅ Нашел пункты в городе *{escape_markdown(city.capitalize())}*:"
            if district and any(district in p.get('address', '').lower() for p in points_to_show):
                header = f"✅ Нашел пункты в районе *{escape_markdown(district.capitalize())}*:"
            
            response = format_points_response(points_to_show, header)
            
            markup = types.InlineKeyboardMarkup()
            markup.add(types.InlineKeyboardButton("🔄 Показать другие варианты", callback_data=f"more_points_{random.randint(1,1000)}"))
            bot.edit_message_text(response, call.message.chat.id, call.message.message_id, parse_mode='MarkdownV2', reply_markup=markup)

        elif data in ['subscribe_tip', 'unsubscribe_tip']:
            # ... (логика подписки) ...
            if data == 'subscribe_tip':
                db.add_subscriber(user_id)
                bot.answer_callback_query(call.id, text="Отлично! Вы подписались на рассылку.")
                bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=None)
            else: # unsubscribe_tip
                db.remove_subscriber(user_id)
                bot.answer_callback_query(call.id, text="Вы отписались от рассылки.")
                bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=None)

        elif data.startswith('show_challenge_'):
            # ... (логика челленджей) ...
            challenge_id = data.replace('show_challenge_', '')
            info = challenges.CHALLENGES[challenge_id]
            response = f"*{info['title']}*\n\n{info['description']}\n\nДлительность: {info['duration_days']} дней. Принять вызов?"
            markup = types.InlineKeyboardMarkup()
            markup.add(types.InlineKeyboardButton("✅ Принять!", callback_data=f"accept_challenge_{challenge_id}"), types.InlineKeyboardButton("⬅️ Назад", callback_data="show_all_challenges"))
            bot.edit_message_text(chat_id=call.message.chat.id, message_id=call.message.message_id, text=response, parse_mode='Markdown', reply_markup=markup)
        elif data.startswith('accept_challenge_'):
            challenge_id = data.replace('accept_challenge_', '')
            db.start_challenge(user_id, challenge_id)
            bot.edit_message_text(chat_id=call.message.chat.id, message_id=call.message.message_id, text=challenges.CHALLENGES[challenge_id]['start_message'])
        elif data == 'show_all_challenges':
            show_all_challenges(call.message.chat.id, edit_message_id=call.message.message_id)
        
        elif data == 'cancel_action':
            bot.delete_message(call.message.chat.id, call.message.message_id)
            bot.send_message(call.message.chat.id, "Отлично! Продолжаем! 💪")
            
        elif data.startswith('search_context_'):
            material = data.replace('search_context_', '')
            bot.answer_callback_query(call.id, f"Ищу пункты для '{material}'...")
            bot.send_message(call.message.chat.id, f"В каком городе найти пункты для *{escape_markdown(material)}*?", parse_mode='MarkdownV2')
    except Exception as e:
        logging.error(f"Ошибка в callback_query_handler: {e}", exc_info=True)

# --- ЗАПУСК БОТА ---
if __name__ == "__main__":
    logging.info("Загрузка данных...")
    points_df, knowledge_base, interesting_facts, eco_tips = load_data()
    
    scheduler = BackgroundScheduler(timezone="Europe/Moscow")
    scheduler.add_job(check_challenges, 'cron', hour=10)
    scheduler.add_job(send_daily_tip, 'cron', hour=11)
    scheduler.start()
    logging.info("Планировщик запущен.")
    
    logging.info("Бот (в режиме polling) запущен...")
    try:
        bot.polling(none_stop=True)
    except Exception as e:
        logging.critical(f"Бот остановился из-за критической ошибки: {e}")
        scheduler.shutdown()