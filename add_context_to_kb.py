import json

# === НАСТРОЙКА ===
# Пути к вашим файлам
INPUT_FILE = './data/knowledge_base.json'
OUTPUT_FILE = './data/knowledge_base_with_context.json'

# Словарь синонимов, по которому мы будем искать ключевые слова в ответах.
SYNONYM_MAP = {
    'бутылки': ['бутылк', 'пэт', 'пластик'],
    'пластик': ['пластик', 'пэт', 'бутылк', 'hdpe', 'пнд'],
    'батарейки': ['батарейк', 'аккумулятор'],
    'бумага': ['бумаг', 'макулатур', 'картон', 'книг'],
    'стекло': ['стекл', 'банк'],
    'одежда': ['одежд', 'вещи', 'текстиль'],
    'металл': ['металл', 'жестян', 'алюмин'],
    'крышки': ['крышк'],
    'техника': ['техник', 'электроника', 'бытовая техника'],
    'опасные отходы': ['опасные отходы', 'ртуть', 'градусник', 'лампочк', 'лампа']
}

print("Начинаем обработку базы знаний...")

try:
    with open(INPUT_FILE, 'r', encoding='utf-8') as f:
        knowledge_base = json.load(f)
except FileNotFoundError:
    print(f"Ошибка: Не удалось найти файл {INPUT_FILE}")
    exit()

processed_count = 0
new_knowledge_base = []

# Проходим по каждой записи (вопрос-ответ) в базе
for item in knowledge_base:
    question = item.get('question', '').lower()
    answer = item.get('answer', '').lower()
    
    found_context = None
    
    # Ищем ключевое слово в ответе
    for context_key, search_terms in SYNONYM_MAP.items():
        for term in search_terms:
            if term in answer:
                found_context = context_key # Нашли! Запоминаем главный синоним
                break
        if found_context:
            break
            
    # Если контекст был найден, добавляем его в запись
    if found_context:
        # Проверяем, чтобы это поле еще не существовало
        if 'context_keyword' not in item:
            item['context_keyword'] = found_context
            processed_count += 1
            print(f"  -> Добавлен контекст '{found_context}' для вопроса: '{item['question'][:50]}...'")

    new_knowledge_base.append(item)

# Сохраняем результат в НОВЫЙ файл, чтобы не повредить исходный
with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
    json.dump(new_knowledge_base, f, ensure_ascii=False, indent=2)

print("\nОбработка завершена!")
print(f"Всего обработано записей: {len(new_knowledge_base)}")
print(f"Добавлено новых полей 'context_keyword': {processed_count}")
print(f"Результат сохранен в файл: {OUTPUT_FILE}")
print("\nТеперь вы можете переименовать 'knowledge_base_with_context.json' в 'knowledge_base.json', чтобы использовать его в боте.")