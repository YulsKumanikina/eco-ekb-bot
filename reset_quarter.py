# reset_quarter.py
import sqlite3
import logging
from config import DB_PATH

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')

def reset_quarterly_points():
    logging.info("Starting quarterly points reset...")
    try:
        conn = sqlite3.connect(DB_PATH)
        cursor = conn.cursor()
        
        # Обнуляем только квартальные очки
        cursor.execute("UPDATE user_profiles SET quarterly_points = 0")
        
        updated_rows = cursor.rowcount
        conn.commit()
        conn.close()
        
        logging.info(f"Successfully reset quarterly points for {updated_rows} users.")
    except Exception as e:
        logging.error(f"An error occurred: {e}")

if __name__ == "__main__":
    reset_quarterly_points()