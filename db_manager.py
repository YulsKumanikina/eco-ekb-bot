# db_manager.py 

import sqlite3
from datetime import date
from config import DB_PATH

def get_connection():
    """Возвращает соединение с базой данных."""
    conn = sqlite3.connect(DB_PATH)
    return conn

def init_db():
    """Инициализирует базу данных и создает таблицы, если их нет."""
    conn = get_connection()
    cursor = conn.cursor()
    
    # ... (таблицы user_challenges, subscribers без изменений) ...
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS user_challenges (
            user_id INTEGER PRIMARY KEY,
            challenge_id TEXT NOT NULL,
            start_date TEXT NOT NULL
        )
    ''')
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS subscribers (
            user_id INTEGER PRIMARY KEY
        )
    ''')

    # ### ОБНОВЛЕННАЯ ТАБЛИЦА ПРОФИЛЕЙ ###
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS user_profiles (
            user_id INTEGER PRIMARY KEY,
            total_points INTEGER DEFAULT 0,
            quarterly_points INTEGER DEFAULT 0,
            level INTEGER DEFAULT 1,
            
            recycle_report_count INTEGER DEFAULT 0,
            last_recycle_report_date TEXT,
            recycle_streak_count INTEGER DEFAULT 0,
            
            challenges_completed_count INTEGER DEFAULT 0,
            
            last_quiz_date TEXT,
            quiz_correct_streak INTEGER DEFAULT 0,
            
            last_tip_date TEXT,
            
            -- Реферальная система
            referred_by INTEGER,
            referrals_count INTEGER DEFAULT 0,
            referrer_bonus_given INTEGER DEFAULT 0 -- 0 = нет, 1 = да
        )
    ''')
    
    # ... (таблица user_achievements без изменений) ...
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS user_achievements (
            user_id INTEGER NOT NULL,
            achievement_id TEXT NOT NULL,
            timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, achievement_id)
        )
    ''')

    conn.commit()
    conn.close()
    print("База данных успешно инициализирована (с полной структурой для геймификации).")

def start_challenge(user_id: int, challenge_id: str):
    conn = get_connection()
    cursor = conn.cursor()
    today = date.today().isoformat()
    cursor.execute('INSERT OR REPLACE INTO user_challenges VALUES (?, ?, ?)', (user_id, challenge_id, today))
    conn.commit()
    conn.close()

def get_user_challenge(user_id: int):
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT challenge_id, start_date FROM user_challenges WHERE user_id = ?', (user_id,))
    result = cursor.fetchone()
    conn.close()
    return {"challenge_id": result[0], "start_date": result[1]} if result else None

def get_all_active_challenges():
    conn = get_connection()
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    cursor.execute('SELECT user_id, challenge_id, start_date FROM user_challenges')
    results = cursor.fetchall()
    conn.close()
    return results

def end_challenge(user_id: int):
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute('DELETE FROM user_challenges WHERE user_id = ?', (user_id,))
    conn.commit()
    conn.close()

def add_subscriber(user_id: int):
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute('INSERT OR IGNORE INTO subscribers (user_id) VALUES (?)', (user_id,))
    conn.commit()
    conn.close()

def remove_subscriber(user_id: int):
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute('DELETE FROM subscribers WHERE user_id = ?', (user_id,))
    conn.commit()
    conn.close()

def is_subscribed(user_id: int) -> bool:
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT 1 FROM subscribers WHERE user_id = ?', (user_id,))
    result = cursor.fetchone()
    conn.close()
    return result is not None

def get_all_subscribers() -> list:
    conn = get_connection()
    cursor = conn.cursor()
    results = cursor.execute('SELECT user_id FROM subscribers').fetchall()
    conn.close()
    return [row[0] for row in results]

def get_or_create_user_profile(user_id: int, referred_by: int = None):
    conn = get_connection()
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    cursor.execute("SELECT * FROM user_profiles WHERE user_id = ?", (user_id,))
    profile = cursor.fetchone()
    
    if not profile:
        if referred_by:
            cursor.execute("INSERT INTO user_profiles (user_id, referred_by) VALUES (?, ?)", (user_id, referred_by))
        else:
            cursor.execute("INSERT INTO user_profiles (user_id) VALUES (?)", (user_id,))
        conn.commit()
        cursor.execute("SELECT * FROM user_profiles WHERE user_id = ?", (user_id,))
        profile = cursor.fetchone()
            
    conn.close()
    return dict(profile)

def add_points(user_id: int, points_to_add: int):
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute(
        "UPDATE user_profiles SET total_points = total_points + ?, quarterly_points = quarterly_points + ? WHERE user_id = ?",
        (points_to_add, points_to_add, user_id)
    )
    conn.commit()
    conn.close()

def update_profile_stats(user_id: int, fields_to_update: dict):
    conn = get_connection()
    cursor = conn.cursor()
    
    set_clause = ", ".join([f"{key} = ?" for key in fields_to_update.keys()])
    values = list(fields_to_update.values())
    values.append(user_id)
    
    query = f"UPDATE user_profiles SET {set_clause} WHERE user_id = ?"
    cursor.execute(query, tuple(values))
    conn.commit()
    conn.close()

def grant_achievement(user_id: int, achievement_id: str):
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute("INSERT OR IGNORE INTO user_achievements (user_id, achievement_id) VALUES (?, ?)", (user_id, achievement_id))
    conn.commit()
    conn.close()

def get_user_achievements(user_id: int):
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute("SELECT achievement_id FROM user_achievements WHERE user_id = ?", (user_id,))
    achievements = [row[0] for row in cursor.fetchall()]
    conn.close()
    return achievements
    
def get_leaderboard(limit: int = 5):
    conn = get_connection()
    conn.row_factory = sqlite3.Row
    cursor = conn.cursor()
    cursor.execute("SELECT user_id, quarterly_points FROM user_profiles ORDER BY quarterly_points DESC LIMIT ?", (limit,))
    leaders = cursor.fetchall()
    conn.close()
    return [dict(row) for row in leaders]