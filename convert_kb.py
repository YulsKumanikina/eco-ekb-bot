# convert_kb.py
import csv
import json

# Пути к файлам
csv_file_path = './data/knowledge_base_new.csv'
json_file_path = './data/knowledge_base.json' 

print("Начинаю конвертацию и объединение баз знаний...")

# 1. Сначала загрузим старые знания из JSON, если они есть
try:
    with open(json_file_path, 'r', encoding='utf-8') as f:
        existing_data = json.load(f)
    print(f"Загружено {len(existing_data)} записей из старого JSON.")
except (FileNotFoundError, json.JSONDecodeError):
    existing_data = []
    print("Старый JSON не найден или пуст, создаем новую базу.")

# 2. Теперь читаем новый CSV-файл и добавляем из него данные
new_data = []
try:
    with open(csv_file_path, 'r', encoding='utf-8') as csv_file:
        csv_reader = csv.reader(csv_file)
        
        for row in csv_reader:
            # Пропускаем заголовки или пустые строки
            if not row or row[0].lower() == 'question':
                continue
            
            # Убеждаемся, что в строке есть оба элемента
            if len(row) >= 2:
                question = row[0].strip()
                answer = row[1].strip()
                new_data.append({"question": question, "answer": answer})

    print(f"Прочитано {len(new_data)} новых записей из CSV.")
    
    # 3. Объединяем старые и новые данные, избегая дубликатов вопросов
    
    # Создаем словарь существующих вопросов для быстрой проверки
    existing_questions = {item['question'].lower() for item in existing_data}
    
    unique_new_data = []
    for item in new_data:
        if item['question'].lower() not in existing_questions:
            unique_new_data.append(item)
    
    # Финальный список = старые данные + только уникальные новые
    final_data = existing_data + unique_new_data
    
    print(f"Добавлено {len(unique_new_data)} уникальных записей.")

    # 4. Записываем объединенные данные обратно в JSON-файл
    with open(json_file_path, 'w', encoding='utf-8') as json_file:
        json.dump(final_data, json_file, ensure_ascii=False, indent=4)
        
    print(f"\nКонвертация завершена! ✅")
    print(f"Файл '{json_file_path}' теперь содержит {len(final_data)} записей.")

except FileNotFoundError:
    print(f"Ошибка: Не удалось найти файл {csv_file_path}. Убедитесь, что он существует.")
except Exception as e:
    print(f"Произошла непредвиденная ошибка: {e}")