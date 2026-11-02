"""
NETI_Food 6.0 — цифровая столовая НГТУ НЭТИ + умный постамат.

Большое обновление:
- SQLite вместо полностью временной памяти;
- безопаснее рассчитана корзина: цены и скидка считаются только сервером;
- валидация времени выдачи и количества;
- история заказов по пользователю;
- статистика кухни и постамата;
- автоматическое распределение/проверка занятых ячеек;
- журнал событий заказа;
- health/status API;
- поиск, фильтры, избранное и "быстрые" категории на фронтенде;
- подробная карточка блюда;
- таймлайн заказа;
- современная адаптивная панель студента + кухни;
- режим демо сохраняется, поэтому проект можно запустить одной командой.

Запуск сервера:
    pip install fastapi uvicorn pydantic qrcode pillow
    python app.py

Открыть:
    http://127.0.0.1:8000

Демо-стенд (симулятор повара, тот же файл, без второго скрипта):
    pip install requests
    python app.py --cook 301      # приготовить конкретный заказ
    python app.py --watch         # следить за очередью и готовить по одному
"""

from __future__ import annotations

import base64
import enum
import io
import os
import sqlite3
import threading
import asyncio
import json
import statistics
import csv
import hashlib
import secrets
import time
import re
from typing import Dict
from contextlib import contextmanager, asynccontextmanager
from datetime import datetime, timedelta
from pathlib import Path
from typing import List, Optional

import qrcode
from fastapi import BackgroundTasks, FastAPI, HTTPException, Query, Request, Response
from fastapi.middleware.cors import CORSMiddleware
from fastapi.middleware.gzip import GZipMiddleware
from fastapi.responses import HTMLResponse
from pydantic import BaseModel, Field

try:
    import serial
except ImportError:
    serial = None

APP_TITLE = "NETI_Food — НГТУ НЭТИ"
APP_VERSION = "7.2.0"
DB_PATH = Path(os.getenv("NETI_FOOD_DB", "neti_food.db"))
HARDWARE_PORT = os.getenv("NETI_FOOD_SERIAL_PORT", "COM3")
HARDWARE_BAUD = int(os.getenv("NETI_FOOD_SERIAL_BAUD", "9600"))
CAMPUS_DISCOUNT = 0.05
LOCKER_COUNT = 8
CASHBACK_LUNCHES_TARGET = 5  # «Купи 5 обедов — получи кофе в подарок»
KITCHEN_PREP_SECONDS_PER_ORDER = 45  # среднее время сборки одного заказа поваром
BREAK_DURATION_MIN = 20  # длительность большой перемены, мин
BASELINE_QUEUE_WAIT_MIN = 15  # среднее время ожидания в очереди без UniFood (замер)
TARGET_WAIT_MIN = 1  # целевое время ожидания с UniFood (забор по ячейке)
ADMIN_TOKEN = os.getenv("NETI_FOOD_ADMIN_TOKEN", "demo-admin-token")

API_TOKEN = os.getenv("NETI_FOOD_API_TOKEN", "")
MAX_ORDER_ITEMS = 20
MAX_TOTAL_QUANTITY = 100

PICKUP_SLOTS = [
    "10:00 (Перерыв 1 пара)",
    "11:40 (Большой перерыв)",
    "13:30 (Перерыв 3 пара)",
    "15:10 (Перерыв 4 пара)",
]

class FoodCategory(str, enum.Enum):
    COMBO = "combo"
    SOUPS = "soup"
    HOT = "hot"
    SALADS = "salad"
    PASTRY = "pastry"
    DRINKS = "drink"


class OrderStatus(str, enum.Enum):
    PAID = "PAID"
    COOKING = "COOKING"
    READY = "READY"
    COMPLETED = "COMPLETED"


class KBJU(BaseModel):
    calories: float = 0.0
    proteins: float = 0.0
    fats: float = 0.0
    carbs: float = 0.0


class MenuItem(BaseModel):
    id: int
    name: str
    category: FoodCategory
    description: Optional[str] = ""
    weight_g: str
    price_rub: float
    is_hot: bool = False
    image_url: str = "https://images.unsplash.com/photo-1546069901-ba9599a7e63c?w=700"
    kbju: KBJU = Field(default_factory=KBJU)
    is_vegan: bool = False
    is_lactose_free: bool = False
    allergens: List[str] = Field(default_factory=list)
    stock: int = 40


class CartItemInput(BaseModel):
    item_id: int
    quantity: int = Field(default=1, ge=1, le=20)


class OrderCreate(BaseModel):
    user_id: int = Field(ge=1)
    pickup_time: str
    items: List[CartItemInput]


class Order(BaseModel):
    order_id: int
    user_id: int
    pickup_time: str
    items_summary: str
    has_hot_food: bool
    total_price: float
    total_before_discount: float
    discount_amount: float
    total_calories: float
    allergens: List[str]
    status: OrderStatus
    cell_number: Optional[int] = None
    qr_code: str
    created_at: str
    updated_at: str


class OrderEvent(BaseModel):
    status: str
    title: str
    description: str
    created_at: str
    done: bool


class PromoApply(BaseModel):
    user_id: int = Field(ge=1)
    code: str = Field(min_length=3, max_length=32)

class FavoriteToggle(BaseModel):
    user_id: int = Field(ge=1)
    item_id: int = Field(ge=1)

class ReviewCreate(BaseModel):
    user_id: int = Field(ge=1)
    item_id: int = Field(ge=1)
    rating: int = Field(ge=1, le=5)
    text: str = Field(default="", max_length=500)

class LoyaltyProfile(BaseModel):
    user_id: int = Field(ge=1)
    name: str = Field(default="Студент", max_length=80)


class RegisterInput(BaseModel):
    name: str = Field(min_length=2, max_length=80)
    email: str = Field(min_length=5, max_length=120)
    password: str = Field(min_length=8, max_length=128)


class LoginInput(BaseModel):
    email: str = Field(min_length=5, max_length=120)
    password: str = Field(min_length=8, max_length=128)

class AdminStockUpdate(BaseModel):
    item_id: int = Field(ge=1)
    stock: int = Field(ge=0, le=10000)

class OrderCreateV6(OrderCreate):
    promo_code: Optional[str] = Field(default=None, min_length=3, max_length=32)


class RecommendationRequest(BaseModel):
    user_id: int = Field(ge=1)
    exclude_item_ids: List[int] = Field(default_factory=list)


class AdminAction(BaseModel):
    token: str = Field(min_length=1)


class StockBatchItem(BaseModel):
    item_id: int = Field(ge=1)
    stock: int = Field(ge=0, le=10000)


class StockBatchUpdate(BaseModel):
    token: str = Field(min_length=1)
    items: List[StockBatchItem] = Field(min_length=1, max_length=200)

MENU_DB: List[MenuItem] = [
    MenuItem(id=1, name="Салат «Цезарь»", category=FoodCategory.SALADS, is_hot=False, price_rub=69.0, weight_g="160г",
              description="Филе куриное, помидоры, капуста пекинская, майонез, сыр, сухарики.",
              kbju=KBJU(calories=240, proteins=16, fats=14, carbs=12), allergens=["лактоза", "глютен", "яйцо"],
              image_url="https://images.unsplash.com/photo-1550304943-4f24f54ddde9?w=500&q=80"),
    MenuItem(id=2, name="Салат «Наслаждение»", category=FoodCategory.SALADS, is_hot=False, price_rub=42.0, weight_g="100г",
              description="Филе куриное, картофель, грибы, лук, яйцо куриное, морковь, грецкие орехи, майонез.",
              kbju=KBJU(calories=190, proteins=9, fats=14, carbs=8), allergens=["яйцо", "орехи"],
              image_url="https://images.unsplash.com/photo-1512621776951-a57141f2eefd?w=500&q=80"),
    MenuItem(id=3, name="Салат из свежей капусты с яблоками", category=FoodCategory.SALADS, is_hot=False, price_rub=25.0, weight_g="100г",
              description="Легкий витаминный салат из свежей белокочанной капусты, сочных яблок и заправки.",
              kbju=KBJU(calories=65, proteins=1.2, fats=3.5, carbs=8.5), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1540420773420-3366772f4999?w=500&q=80"),
    MenuItem(id=4, name="Салат «Веснушка»", category=FoodCategory.SALADS, is_hot=False, price_rub=22.0, weight_g="100г",
              description="Освежающий салат с морковью, свежим огурцом и зеленью.",
              kbju=KBJU(calories=70, proteins=1.5, fats=4.0, carbs=7.0), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1546069901-ba9599a7e63c?w=500&q=80"),
    MenuItem(id=5, name="Салат «Крабик»", category=FoodCategory.SALADS, is_hot=False, price_rub=30.0, weight_g="100г",
              description="Классический салат с крабовыми палочками, отварным рисом, сладкой кукурузой и яйцом.",
              kbju=KBJU(calories=160, proteins=5.5, fats=9.5, carbs=14.0), is_lactose_free=True, allergens=["яйцо", "рыба/морепродукты"],
              image_url="https://images.unsplash.com/photo-1598514982205-f36b96d1e8d4?w=500&q=80"),
    MenuItem(id=6, name="Салат «Цезарь Макс»", category=FoodCategory.SALADS, is_hot=False, price_rub=65.0, weight_g="170г",
              description="Увеличенная порция фирменного Цезаря с сочной курицей и сыром.",
              kbju=KBJU(calories=260, proteins=18, fats=15, carbs=13), allergens=["лактоза", "глютен", "яйцо"],
              image_url="https://images.unsplash.com/photo-1550304943-4f24f54ddde9?w=500&q=80"),
    MenuItem(id=7, name="Борщ из свежей капусты с картофелем", category=FoodCategory.SOUPS, is_hot=True, price_rub=25.0, weight_g="250мл",
              description="Традиционный свекольный борщ со свежей капустой и картофелем на мясном бульоне.",
              kbju=KBJU(calories=140, proteins=4.5, fats=6.0, carbs=16.0), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1547592180-85f173990554?w=500&q=80"),
    MenuItem(id=8, name="Борщ Сибирский", category=FoodCategory.SOUPS, is_hot=True, price_rub=35.0, weight_g="300мл",
              description="Насыщенный бодрящий борщ с мягкой говядиной и зеленью.",
              kbju=KBJU(calories=180, proteins=7.0, fats=8.0, carbs=19.0), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1547592180-85f173990554?w=500&q=80"),
    MenuItem(id=9, name="Щи Боярские", category=FoodCategory.SOUPS, is_hot=True, price_rub=35.0, weight_g="300мл",
              description="Ароматные густые щи с квашеной капустой и тушеным мясом.",
              kbju=KBJU(calories=165, proteins=6.0, fats=7.5, carbs=14.0), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1547592166-23ac45744acd?w=500&q=80"),
    MenuItem(id=10, name="Солянка Домашняя", category=FoodCategory.SOUPS, is_hot=True, price_rub=40.0, weight_g="300мл",
              description="Мясной суп с солеными огурчиками, копченостями и маслинами.",
              kbju=KBJU(calories=280, proteins=14, fats=18, carbs=12), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1547592166-23ac45744acd?w=500&q=80"),
    MenuItem(id=11, name="Суп грибной", category=FoodCategory.SOUPS, is_hot=True, price_rub=27.0, weight_g="300мл",
              description="Легкий ароматный суп из лесных грибов с картофелем и перловкой.",
              kbju=KBJU(calories=120, proteins=3.5, fats=4.0, carbs=17.0), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1547592180-85f173990554?w=500&q=80"),
    MenuItem(id=12, name="Рыба аппетитная", category=FoodCategory.HOT, is_hot=True, price_rub=87.0, weight_g="120г",
              description="Филе белой рыбы, запеченное под румяной корочкой.",
              kbju=KBJU(calories=210, proteins=20, fats=12, carbs=4), allergens=["рыба"],
              image_url="https://images.unsplash.com/photo-1519708227418-c8fd9a32b7a2?w=500&q=80"),
    MenuItem(id=13, name="Жаркое по-домашнему (из говядины)", category=FoodCategory.HOT, is_hot=True, price_rub=98.0, weight_g="300г",
              description="Томленая сочная говядина с запеченным картофелем, луком и подливой.",
              kbju=KBJU(calories=520, proteins=26, fats=24, carbs=42), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1544025162-d76694265947?w=500&q=80"),
    MenuItem(id=14, name="Гуляш из говядины", category=FoodCategory.HOT, is_hot=True, price_rub=72.0, weight_g="50/75г",
              description="Нежные кусочки говядины в насыщенном томатно-мясном соусе.",
              kbju=KBJU(calories=230, proteins=18, fats=15, carbs=6), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1534422298391-e4f8c172dddb?w=500&q=80"),
    MenuItem(id=15, name="Запеканка картофельная с мясом", category=FoodCategory.HOT, is_hot=True, price_rub=92.0, weight_g="240г",
              description="Нежное картофельное пюре с сочной мясной начинкой из фарша.",
              kbju=KBJU(calories=390, proteins=17, fats=19, carbs=36), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1541529086526-db283c563270?w=500&q=80"),
    MenuItem(id=16, name="Биточек особый", category=FoodCategory.HOT, is_hot=True, price_rub=52.0, weight_g="80г",
              description="Сочная рубленая котлета из смешанного фарша со специями.",
              kbju=KBJU(calories=210, proteins=14, fats=15, carbs=5), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1529042410759-befb1204b468?w=500&q=80"),
    MenuItem(id=17, name="Оладьи из печени", category=FoodCategory.HOT, is_hot=True, price_rub=62.0, weight_g="100г",
              description="Нежные печеночные оладьи, обжаренные до золотистой корочки.",
              kbju=KBJU(calories=195, proteins=15, fats=10, carbs=9), allergens=["яйцо", "глютен"],
              image_url="https://images.unsplash.com/photo-1565299585323-38d6b0865b47?w=500&q=80"),
    MenuItem(id=18, name="Филе куриное запеченное с помидором и сыром", category=FoodCategory.HOT, is_hot=True, price_rub=77.0, weight_g="100г",
              description="Куриное филе под кружочками свежих томатов и расплавленной сырной шапкой.",
              kbju=KBJU(calories=220, proteins=24, fats=12, carbs=3), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1604908176997-125f25cc6f3d?w=500&q=80"),
    MenuItem(id=19, name="Пельмени фри", category=FoodCategory.HOT, is_hot=True, price_rub=55.0, weight_g="200г",
              description="Обжаренные во фритюре хрустящие пельмени с мясным фаршем.",
              kbju=KBJU(calories=420, proteins=16, fats=22, carbs=38), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1525059696034-4967a8e1dca2?w=500&q=80"),
    MenuItem(id=20, name="Бифштекс с яйцом", category=FoodCategory.HOT, is_hot=True, price_rub=60.0, weight_g="75/20г",
              description="Натуральный котлетный бифштекс, украшенный обжаренным яйцом-глазуньей.",
              kbju=KBJU(calories=280, proteins=22, fats=20, carbs=2), allergens=["яйцо"],
              image_url="https://images.unsplash.com/photo-1544025162-d76694265947?w=500&q=80"),
    MenuItem(id=21, name="Плов со свининой", category=FoodCategory.HOT, is_hot=True, price_rub=65.0, weight_g="250г",
              description="Рассыпчатый длиннозерный рис со свининой, морковью и восточными специями.",
              kbju=KBJU(calories=480, proteins=18, fats=20, carbs=55), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1512058564366-18510be2db19?w=500&q=80"),
    MenuItem(id=22, name="Горбуша запечённая с помидором", category=FoodCategory.HOT, is_hot=True, price_rub=55.0, weight_g="75г",
              description="Сочное филе красной рыбы, запеченное со свежим томатом.",
              kbju=KBJU(calories=145, proteins=17, fats=7, carbs=2), allergens=["рыба"],
              image_url="https://images.unsplash.com/photo-1519708227418-c8fd9a32b7a2?w=500&q=80"),
    MenuItem(id=23, name="Филе куриное запечённое", category=FoodCategory.HOT, is_hot=True, price_rub=60.0, weight_g="75г",
              description="Диетическое запеченное филе цыпленка в лёгком маринаде со специями.",
              kbju=KBJU(calories=130, proteins=22, fats=4, carbs=1), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1604908176997-125f25cc6f3d?w=500&q=80"),
    MenuItem(id=24, name="Эскалоп из свинины в сыре", category=FoodCategory.HOT, is_hot=True, price_rub=65.0, weight_g="75г",
              description="Бескостный кусочек свинины, запеченный под толстым слоем сыра.",
              kbju=KBJU(calories=260, proteins=19, fats=20, carbs=2), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1544025162-d76694265947?w=500&q=80"),
    MenuItem(id=25, name="Котлета Домашняя", category=FoodCategory.HOT, is_hot=True, price_rub=35.0, weight_g="75г",
              description="Сочная классическая котлета из говядины и свинины.",
              kbju=KBJU(calories=190, proteins=12, fats=14, carbs=6), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1529042410759-befb1204b468?w=500&q=80"),
    MenuItem(id=26, name="Ежик куриный", category=FoodCategory.HOT, is_hot=True, price_rub=32.0, weight_g="50г",
              description="Нежные тефтели из куриного фарша с добавлением отварного риса.",
              kbju=KBJU(calories=110, proteins=9, fats=5, carbs=7), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1529042410759-befb1204b468?w=500&q=80"),
    MenuItem(id=27, name="Сосиска жареная", category=FoodCategory.HOT, is_hot=True, price_rub=20.0, weight_g="1 шт",
              description="Сочная обжаренная молочная сосиска.",
              kbju=KBJU(calories=130, proteins=5, fats=12, carbs=1), is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1541529086526-db283c563270?w=500&q=80"),
    MenuItem(id=28, name="Манты", category=FoodCategory.HOT, is_hot=True, price_rub=20.0, weight_g="1 шт",
              description="Традиционный мант на пару с начинкой из сочного мясного фарша и лука.",
              kbju=KBJU(calories=140, proteins=6, fats=7, carbs=13), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1525059696034-4967a8e1dca2?w=500&q=80"),
    MenuItem(id=29, name="Каша молочная манная", category=FoodCategory.HOT, is_hot=True, price_rub=24.0, weight_g="200г",
              description="Нежная манная каша на натуральном молоке с кусочком сливочного масла.",
              kbju=KBJU(calories=190, proteins=5, fats=6, carbs=29), allergens=["лактоза", "глютен"],
              image_url="https://images.unsplash.com/photo-1517673400267-0251440c45dc?w=500&q=80"),
    MenuItem(id=30, name="Омлет натуральный", category=FoodCategory.HOT, is_hot=True, price_rub=30.0, weight_g="120г",
              description="Пышный классический запеченный омлет из свежих куриных яиц и молока.",
              kbju=KBJU(calories=180, proteins=11, fats=14, carbs=2), allergens=["яйцо", "лактоза"],
              image_url="https://images.unsplash.com/photo-1525351484163-7529414344d8?w=500&q=80"),
    MenuItem(id=31, name="Запеканка творожная с изюмом", category=FoodCategory.HOT, is_hot=True, price_rub=55.0, weight_g="120г",
              description="Сладкая запеканка из натурального фермерского творога со сладким изюмом.",
              kbju=KBJU(calories=240, proteins=16, fats=8, carbs=26), allergens=["лактоза", "яйцо"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=32, name="Пюре картофельное", category=FoodCategory.HOT, is_hot=True, price_rub=39.0, weight_g="150г",
              description="Воздушное картофельное пюре со сливочным маслом и молоком.",
              kbju=KBJU(calories=160, proteins=3, fats=5, carbs=25), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1541529086526-db283c563270?w=500&q=80"),
    MenuItem(id=33, name="Картофельное пюре (200г)", category=FoodCategory.HOT, is_hot=True, price_rub=26.0, weight_g="200г",
              description="Большая порция классического домашнего пюре.",
              kbju=KBJU(calories=210, proteins=4, fats=6, carbs=34), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1541529086526-db283c563270?w=500&q=80"),
    MenuItem(id=34, name="Картофель запеченный", category=FoodCategory.HOT, is_hot=True, price_rub=34.0, weight_g="200г",
              description="Дольки картофеля, запеченные до румяной корочки с ароматными травами.",
              kbju=KBJU(calories=190, proteins=3.5, fats=4.5, carbs=33), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1544025162-d76694265947?w=500&q=80"),
    MenuItem(id=35, name="Капуста тушеная", category=FoodCategory.HOT, is_hot=True, price_rub=29.0, weight_g="150г",
              description="Нежная тушеная капуста с томатом и морковью.",
              kbju=KBJU(calories=95, proteins=2, fats=4, carbs=12), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1540420773420-3366772f4999?w=500&q=80"),
    MenuItem(id=36, name="Каша гречневая рассыпчатая с маслом", category=FoodCategory.HOT, is_hot=True, price_rub=23.0, weight_g="150г",
              description="Отварная гречневая крупа с добавлением сливочного масла.",
              kbju=KBJU(calories=175, proteins=5.5, fats=4.5, carbs=28), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1512058564366-18510be2db19?w=500&q=80"),
    MenuItem(id=37, name="Макароны отварные с маслом", category=FoodCategory.HOT, is_hot=True, price_rub=23.0, weight_g="150г",
              description="Макароны из твердых сортов пшеницы со сливочным маслом.",
              kbju=KBJU(calories=210, proteins=6, fats=5, carbs=35), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1551183053-bf91a1d81141?w=500&q=80"),
    MenuItem(id=38, name="Рис по-мексикански", category=FoodCategory.HOT, is_hot=True, price_rub=26.0, weight_g="200г",
              description="Ароматный рис с добавлением кукурузы, зеленый горошка и сладкого перца.",
              kbju=KBJU(calories=230, proteins=4.5, fats=4.0, carbs=44), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1512058564366-18510be2db19?w=500&q=80"),
    MenuItem(id=39, name="Обед студента (сосиска, пюре)", category=FoodCategory.COMBO, is_hot=True, price_rub=32.0, weight_g="180г",
              description="Легендарный студенческий комбо-набор: молочная сосиска и картофельное пюре.",
              kbju=KBJU(calories=320, proteins=9, fats=14, carbs=38), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1541529086526-db283c563270?w=500&q=80"),
    MenuItem(id=40, name="Гамбургер с курицей", category=FoodCategory.COMBO, is_hot=True, price_rub=69.0, weight_g="190г",
              description="Пышная кунжутная булочка, запеченное куриное филе, томаты, свежая капуста и соус.",
              kbju=KBJU(calories=450, proteins=22, fats=16, carbs=52), is_lactose_free=True, allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1568901346375-23c9450c58cd?w=500&q=80"),
    MenuItem(id=41, name="Гамбургер с ветчиной", category=FoodCategory.COMBO, is_hot=True, price_rub=54.0, weight_g="180г",
              description="Сочная булочка, ломтики ветчины, сыр, свежие овощи.",
              kbju=KBJU(calories=410, proteins=17, fats=18, carbs=46), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1568901346375-23c9450c58cd?w=500&q=80"),
    MenuItem(id=42, name="Сэндвич с курицей", category=FoodCategory.COMBO, is_hot=False, price_rub=62.0, weight_g="160г",
              description="Сэндвич на тостовом хлебе с куриным филе, листьями салата и соусом.",
              kbju=KBJU(calories=360, proteins=19, fats=12, carbs=42), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509722747041-616f39b57569?w=500&q=80"),
    MenuItem(id=43, name="Сэндвич с ветчиной/колбасой", category=FoodCategory.COMBO, is_hot=False, price_rub=57.0, weight_g="150г",
              description="Классический закрытый сэндвич с ветчиной и свежими огурчиками.",
              kbju=KBJU(calories=340, proteins=13, fats=15, carbs=38), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509722747041-616f39b57569?w=500&q=80"),
    MenuItem(id=44, name="Сэндвич с бифштексом", category=FoodCategory.COMBO, is_hot=True, price_rub=60.0, weight_g="165г",
              description="Сытный сэндвич с мясным бифштексом и пикантным соусом.",
              kbju=KBJU(calories=410, proteins=20, fats=17, carbs=43), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509722747041-616f39b57569?w=500&q=80"),
    MenuItem(id=45, name="Хот-дог", category=FoodCategory.COMBO, is_hot=True, price_rub=42.0, weight_g="200г",
              description="Горячая булочка с сочной сосиской, кетчупом и горчичным соусом.",
              kbju=KBJU(calories=380, proteins=12, fats=16, carbs=45), allergens=["глютен", "горчица"],
              image_url="https://images.unsplash.com/photo-1627308595229-7830a5c91f9f?w=500&q=80"),
    MenuItem(id=46, name="Пицца с колбасой", category=FoodCategory.PASTRY, is_hot=True, price_rub=45.0, weight_g="120г",
              description="Запеченная порционная пицца с соусом, колбасой и расплавленным сыром.",
              kbju=KBJU(calories=340, proteins=14, fats=16, carbs=38), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1565299624946-b28f40a0ae38?w=500&q=80"),
    MenuItem(id=47, name="Пицца (170г)", category=FoodCategory.PASTRY, is_hot=True, price_rub=75.0, weight_g="170г",
              description="Большая студенческая пицца с ветчиной, сыром и томатами.",
              kbju=KBJU(calories=460, proteins=19, fats=21, carbs=48), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1565299624946-b28f40a0ae38?w=500&q=80"),
    MenuItem(id=48, name="Самса с курицей", category=FoodCategory.PASTRY, is_hot=True, price_rub=49.0, weight_g="140г",
              description="Хрустящая восточная выпечка с сочной курицей и луком.",
              kbju=KBJU(calories=370, proteins=16, fats=18, carbs=35), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=49, name="Слойка с ветчиной и сыром", category=FoodCategory.PASTRY, is_hot=True, price_rub=40.0, weight_g="80г",
              description="Слоеное тесто с начинкой из ветчины и тянущегося сыра.",
              kbju=KBJU(calories=270, proteins=9, fats=15, carbs=25), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=50, name="Слойка с курицей и грибами", category=FoodCategory.PASTRY, is_hot=True, price_rub=30.0, weight_g="80г",
              description="Горячая слойка с жульеном из куриного филе и шампиньонов.",
              kbju=KBJU(calories=250, proteins=10, fats=13, carbs=23), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=51, name="Беляш с мясом", category=FoodCategory.PASTRY, is_hot=True, price_rub=30.0, weight_g="140г",
              description="Традиционный жареный беляш с сочным фаршем из говядины.",
              kbju=KBJU(calories=390, proteins=14, fats=22, carbs=34), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=52, name="Сосиска в тесте", category=FoodCategory.PASTRY, is_hot=True, price_rub=30.0, weight_g="120г",
              description="Запеченная в пышном дрожжевом тесте сочная сосиска.",
              kbju=KBJU(calories=310, proteins=10, fats=14, carbs=35), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1541529086526-db283c563270?w=500&q=80"),
    MenuItem(id=53, name="Хачапури", category=FoodCategory.PASTRY, is_hot=True, price_rub=22.0, weight_g="90г",
              description="Грузинская выпечка с нежной начинкой из расплавленного сыра.",
              kbju=KBJU(calories=260, proteins=11, fats=12, carbs=27), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=54, name="Слойка с брусникой", category=FoodCategory.PASTRY, is_hot=False, price_rub=18.0, weight_g="50г",
              description="Слоеная выпечка со сладковато-терпким брусничным джемом.",
              kbju=KBJU(calories=160, proteins=2.5, fats=7, carbs=22), is_lactose_free=True, allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=55, name="Слойка с вишней", category=FoodCategory.PASTRY, is_hot=False, price_rub=25.0, weight_g="80г",
              description="Ароматная слойка с вишневым конфитюром.",
              kbju=KBJU(calories=230, proteins=3.5, fats=9, carbs=33), is_lactose_free=True, allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=56, name="Булочка с корицей", category=FoodCategory.PASTRY, is_hot=False, price_rub=13.0, weight_g="60г",
              description="Сдобная завитая булочка с корицей и сахаром.",
              kbju=KBJU(calories=190, proteins=4, fats=5, carbs=32), allergens=["глютен"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=57, name="Ватрушка с творогом", category=FoodCategory.PASTRY, is_hot=False, price_rub=21.0, weight_g="75г",
              description="Классическая румяная ватрушка с начинкой из натурального творога.",
              kbju=KBJU(calories=210, proteins=8, fats=6, carbs=30), allergens=["глютен", "лактоза"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=58, name="Сочень с творогом", category=FoodCategory.PASTRY, is_hot=False, price_rub=27.0, weight_g="100г",
              description="Песочный сочень с нежной творожной начинкой.",
              kbju=KBJU(calories=280, proteins=9, fats=10, carbs=38), allergens=["глютен", "лактоза", "яйцо"],
              image_url="https://images.unsplash.com/photo-1509440159596-0249088772ff?w=500&q=80"),
    MenuItem(id=59, name="Компот из черной смородины", category=FoodCategory.DRINKS, is_hot=False, price_rub=15.0, weight_g="150мл",
              description="Натуральный освежающий компот из ягод черной смородины.",
              kbju=KBJU(calories=60, proteins=0.2, fats=0.1, carbs=14), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1544787219-7f47ccb76574?w=500&q=80"),
    MenuItem(id=60, name="Сок «Добрый»", category=FoodCategory.DRINKS, is_hot=False, price_rub=15.0, weight_g="150мл",
              description="Порционный фруктовый сок в ассортименте (яблоко/апельсин/мультифрукт).",
              kbju=KBJU(calories=70, proteins=0.5, fats=0.0, carbs=16), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1613478223719-2ab802602423?w=500&q=80"),
    MenuItem(id=61, name="Чай «Гринфилд»", category=FoodCategory.DRINKS, is_hot=True, price_rub=10.0, weight_g="200мл",
              description="Горячий пакетированный чай (черный / зеленый / бергамот).",
              kbju=KBJU(calories=2, proteins=0, fats=0, carbs=0), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1544787219-7f47ccb76574?w=500&q=80"),
    MenuItem(id=62, name="Чай «Тесс» в ассортименте", category=FoodCategory.DRINKS, is_hot=True, price_rub=9.0, weight_g="200мл",
              description="Ароматный горячий чай Tess с добавлением трав или ягод.",
              kbju=KBJU(calories=2, proteins=0, fats=0, carbs=0), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1544787219-7f47ccb76574?w=500&q=80"),
    MenuItem(id=63, name="Кофе Черный", category=FoodCategory.DRINKS, is_hot=True, price_rub=16.0, weight_g="200мл",
              description="Бодрящий горячий черный кофе.",
              kbju=KBJU(calories=5, proteins=0.2, fats=0.0, carbs=0.8), is_vegan=True, is_lactose_free=True,
              image_url="https://images.unsplash.com/photo-1514432324607-a09d9b4aefdd?w=500&q=80"),
    MenuItem(id=64, name="Кофе «3 в 1»", category=FoodCategory.DRINKS, is_hot=True, price_rub=12.0, weight_g="200мл",
              description="Растворимый кофейный напиток с сахаром и сливками.",
              kbju=KBJU(calories=80, proteins=1, fats=2, carbs=14), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1514432324607-a09d9b4aefdd?w=500&q=80"),
    MenuItem(id=65, name="Горячий шоколад", category=FoodCategory.DRINKS, is_hot=True, price_rub=15.0, weight_g="200мл",
              description="Густой согревающий напиток с насыщенным вкусом какао.",
              kbju=KBJU(calories=130, proteins=3.5, fats=4.5, carbs=19), allergens=["лактоза"],
              image_url="https://images.unsplash.com/photo-1542990253-0d0f5be5f0ed?w=500&q=80"),
]
MENU_BY_ID: Dict[int, MenuItem] = {item.id: item for item in MENU_DB}

db_lock = threading.RLock()


def now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


@contextmanager
def db():
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA busy_timeout=10000")
    conn.execute("PRAGMA foreign_keys=ON")
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


NETI_EXTRA_DB = Path(os.getenv("NETI_FOOD_EXTRA_DB", "neti_food_extra.db"))


@contextmanager
def extra_db():
    """Context manager for the 'extra' (loyalty/social) database.

    NOTE (fixed): this used to return a bare sqlite3.Connection object.
    sqlite3.Connection's own context-manager protocol commits/rolls back
    on exit but never closes the connection, so every
    ``with db_lock, extra_db() as conn:`` call leaked a file handle.
    Wrapping it in @contextmanager with an explicit close() in `finally`
    fixes the leak, matching the main db() helper above.
    """
    conn = sqlite3.connect(NETI_EXTRA_DB, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA busy_timeout=10000")
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def init_db() -> None:
    with db_lock, db() as conn:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS menu_stock (
                item_id INTEGER PRIMARY KEY,
                stock INTEGER NOT NULL DEFAULT 40
            );

            CREATE TABLE IF NOT EXISTS orders (
                order_id INTEGER PRIMARY KEY,
                user_id INTEGER NOT NULL,
                pickup_time TEXT NOT NULL,
                items_json TEXT NOT NULL,
                items_summary TEXT NOT NULL,
                has_hot_food INTEGER NOT NULL,
                total_price REAL NOT NULL,
                total_before_discount REAL NOT NULL,
                discount_amount REAL NOT NULL,
                total_calories REAL NOT NULL,
                allergens_json TEXT NOT NULL,
                status TEXT NOT NULL,
                cell_number INTEGER,
                qr_code TEXT NOT NULL,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS order_events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                order_id INTEGER NOT NULL,
                status TEXT NOT NULL,
                title TEXT NOT NULL,
                description TEXT NOT NULL,
                created_at TEXT NOT NULL
            );

            CREATE INDEX IF NOT EXISTS idx_orders_user
            ON orders(user_id);

            CREATE INDEX IF NOT EXISTS idx_orders_status
            ON orders(status);

            CREATE INDEX IF NOT EXISTS idx_order_events_order_created
            ON order_events(order_id, created_at);
            """
        )

        count = conn.execute("SELECT COUNT(*) AS c FROM menu_stock").fetchone()["c"]
        if count == 0:
            conn.executemany(
                "INSERT INTO menu_stock(item_id, stock) VALUES (?, ?)",
                [(item.id, item.stock) for item in MENU_DB],
            )


def menu_with_stock() -> List[MenuItem]:
    with db_lock, db() as conn:
        stock_map = {
            row["item_id"]: row["stock"]
            for row in conn.execute("SELECT item_id, stock FROM menu_stock")
        }
    return [
        item.model_copy(update={"stock": stock_map.get(item.id, item.stock)})
        for item in MENU_DB
    ]


def get_menu_item(item_id: int) -> MenuItem:
    item = MENU_BY_ID.get(item_id)
    if item is None:
        raise HTTPException(404, f"Блюдо #{item_id} не найдено")
    stock = item.stock
    with db_lock, db() as conn:
        row = conn.execute(
            "SELECT stock FROM menu_stock WHERE item_id = ?", (item_id,)
        ).fetchone()
        if row:
            stock = row["stock"]
    return item.model_copy(update={"stock": stock})


def generate_qr(payload: str) -> str:
    qr = qrcode.QRCode(version=1, box_size=9, border=4)
    qr.add_data(payload)
    qr.make(fit=True)
    img = qr.make_image(fill_color="black", back_color="white")
    buf = io.BytesIO()
    img.save(buf, format="PNG")
    return base64.b64encode(buf.getvalue()).decode("utf-8")


def row_to_order(row: sqlite3.Row) -> Order:
    return Order(
        order_id=row["order_id"],
        user_id=row["user_id"],
        pickup_time=row["pickup_time"],
        items_summary=row["items_summary"],
        has_hot_food=bool(row["has_hot_food"]),
        total_price=row["total_price"],
        total_before_discount=row["total_before_discount"],
        discount_amount=row["discount_amount"],
        total_calories=row["total_calories"],
        allergens=json.loads(row["allergens_json"]),
        status=OrderStatus(row["status"]),
        cell_number=row["cell_number"],
        qr_code=row["qr_code"],
        created_at=row["created_at"],
        updated_at=row["updated_at"],
    )


def get_order(order_id: int) -> Order:
    with db_lock, db() as conn:
        row = conn.execute(
            "SELECT * FROM orders WHERE order_id = ?", (order_id,)
        ).fetchone()
    if not row:
        raise HTTPException(404, "Заказ не найден")
    return row_to_order(row)


def add_event(order_id: int, status_value: str, title: str, description: str) -> None:
    with db_lock, db() as conn:
        conn.execute(
            """
            INSERT INTO order_events(order_id, status, title, description, created_at)
            VALUES (?, ?, ?, ?, ?)
            """,
            (order_id, status_value, title, description, now_iso()),
        )


def update_order_status(
    order_id: int,
    new_status: OrderStatus,
    *,
    cell_number: Optional[int] = None,
) -> Order:
    timestamp = now_iso()
    with db_lock, db() as conn:
        row = conn.execute(
            "SELECT * FROM orders WHERE order_id = ?", (order_id,)
        ).fetchone()
        if not row:
            raise HTTPException(404, "Заказ не найден")

        old = OrderStatus(row["status"])

        allowed = {
            OrderStatus.PAID: {OrderStatus.COOKING},
            OrderStatus.COOKING: {OrderStatus.READY},
            OrderStatus.READY: {OrderStatus.COMPLETED},
            OrderStatus.COMPLETED: set(),
        }

        if new_status not in allowed[old]:
            raise HTTPException(
                400,
                f"Нельзя перевести заказ из {old.value} в {new_status.value}",
            )

        conn.execute(
            """
            UPDATE orders
            SET status = ?, cell_number = ?, updated_at = ?
            WHERE order_id = ?
            """,
            (
                new_status.value,
                cell_number,
                timestamp,
                order_id,
            ),
        )

    titles = {
        OrderStatus.COOKING: ("Заказ принят кухней", "Повара начали приготовление."),
        OrderStatus.READY: ("Заказ готов", f"Заказ помещён в ячейку №{cell_number}."),
        OrderStatus.COMPLETED: ("Заказ получен", "Заказ забран из постамата."),
    }
    title, description = titles[new_status]
    add_event(order_id, new_status.value, title, description)
    try:
        updated_order = get_order(order_id)
        add_notification(updated_order.user_id, title, description)
    except Exception:
        pass
    return get_order(order_id)

async def send_to_hardware_async(box_number: int, state: str = "ON") -> None:
    def _send():
        if serial is None:
            print(
                f"[ПОСТАМАТ] Демо-режим: ячейка #{box_number} -> {state}"
            )
            return
        try:
            with serial.Serial(
                HARDWARE_PORT, HARDWARE_BAUD, timeout=1
            ) as ser:
                ser.write(
                    f"CELL_{state}:{box_number}\n".encode("utf-8")
                )
        except Exception as exc:
            print(f"[ПОСТАМАТ] Ошибка контроллера: {exc}")

    await asyncio.to_thread(_send)


def occupied_cells() -> dict[int, Order]:
    result: dict[int, Order] = {}
    with db_lock, db() as conn:
        rows = conn.execute(
            """
            SELECT * FROM orders
            WHERE status = 'READY' AND cell_number IS NOT NULL
            ORDER BY cell_number
            """
        ).fetchall()
    for row in rows:
        result[int(row["cell_number"])] = row_to_order(row)
    return result


def free_cells() -> List[int]:
    occupied = set(occupied_cells())
    return [n for n in range(1, LOCKER_COUNT + 1) if n not in occupied]


def init_extra_db():
    """Create the extended database in dependency-safe order.

    Important: SQLite cannot create an index for a table that does not exist.
    The old build created several indexes before favorites/reviews/etc., which
    caused startup to fail with: no such table: main.favorites.
    """
    with db_lock, extra_db() as conn:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA busy_timeout=10000")
        conn.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            user_id INTEGER PRIMARY KEY,
            name TEXT NOT NULL DEFAULT 'Студент',
            email TEXT UNIQUE,
            password_hash TEXT,
            points INTEGER NOT NULL DEFAULT 0,
            level TEXT NOT NULL DEFAULT 'NEW',
            created_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS sessions (
            token_hash TEXT PRIMARY KEY,
            user_id INTEGER NOT NULL,
            created_at TEXT NOT NULL,
            expires_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS idempotency_keys (
            user_id INTEGER NOT NULL,
            idem_key TEXT NOT NULL,
            order_id INTEGER NOT NULL,
            created_at TEXT NOT NULL,
            PRIMARY KEY(user_id, idem_key)
        );

        CREATE TABLE IF NOT EXISTS favorites (
            user_id INTEGER NOT NULL,
            item_id INTEGER NOT NULL,
            created_at TEXT NOT NULL,
            PRIMARY KEY(user_id, item_id)
        );

        CREATE TABLE IF NOT EXISTS reviews (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            item_id INTEGER NOT NULL,
            rating INTEGER NOT NULL CHECK(rating BETWEEN 1 AND 5),
            text TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS promo_codes (
            code TEXT PRIMARY KEY,
            discount_percent REAL NOT NULL,
            max_uses INTEGER NOT NULL DEFAULT 100,
            used_count INTEGER NOT NULL DEFAULT 0,
            active INTEGER NOT NULL DEFAULT 1
        );

        CREATE TABLE IF NOT EXISTS promo_users (
            code TEXT NOT NULL,
            user_id INTEGER NOT NULL,
            used_at TEXT NOT NULL,
            PRIMARY KEY(code, user_id)
        );

        CREATE TABLE IF NOT EXISTS notifications (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            message TEXT NOT NULL,
            read INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS audit_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            actor TEXT NOT NULL,
            action TEXT NOT NULL,
            details TEXT NOT NULL,
            created_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS cashback_progress (
            user_id INTEGER PRIMARY KEY,
            hot_lunches_count INTEGER NOT NULL DEFAULT 0,
            free_coffees_earned INTEGER NOT NULL DEFAULT 0,
            free_coffees_used INTEGER NOT NULL DEFAULT 0,
            updated_at TEXT NOT NULL
        );

        /* Indexes are deliberately created AFTER their tables. */
        CREATE INDEX IF NOT EXISTS idx_sessions_expires
            ON sessions(expires_at);
        CREATE INDEX IF NOT EXISTS idx_idempotency_created
            ON idempotency_keys(created_at);
        CREATE INDEX IF NOT EXISTS idx_favorites_user_created
            ON favorites(user_id, created_at);
        CREATE INDEX IF NOT EXISTS idx_reviews_item_created
            ON reviews(item_id, created_at);
        CREATE INDEX IF NOT EXISTS idx_reviews_user_created
            ON reviews(user_id, created_at);
        CREATE INDEX IF NOT EXISTS idx_notifications_user_read
            ON notifications(user_id, read, created_at);
        CREATE INDEX IF NOT EXISTS idx_audit_created
            ON audit_log(created_at);
        CREATE INDEX IF NOT EXISTS idx_audit_actor
            ON audit_log(actor);
        """)

        defaults = [
            ("NETI10", 10, 1000),
            ("STUDENT5", 5, 5000),
            ("WELCOME", 7, 1000),
        ]
        for code, discount, uses in defaults:
            conn.execute(
                "INSERT OR IGNORE INTO promo_codes(code, discount_percent, max_uses) VALUES (?,?,?)",
                (code, discount, uses)
            )
        cols = {r["name"] for r in conn.execute("PRAGMA table_info(users)").fetchall()}
        if "email" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN email TEXT")
        if "password_hash" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN password_hash TEXT")
        if "points" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN points INTEGER NOT NULL DEFAULT 0")
        if "level" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN level TEXT NOT NULL DEFAULT 'NEW'")
        if "created_at" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN created_at TEXT")
            conn.execute("UPDATE users SET created_at=? WHERE created_at IS NULL", (now_iso(),))
        conn.execute("DELETE FROM sessions WHERE expires_at < ?", (now_iso(),))


@asynccontextmanager
async def lifespan(app: FastAPI):
    """FastAPI lifespan instead of deprecated @app.on_event('startup')."""
    init_db()
    init_extra_db()
    with db_lock, db() as conn:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA foreign_keys=ON")
        conn.execute("PRAGMA busy_timeout=10000")
    with db_lock, extra_db() as conn:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA busy_timeout=10000")
    yield


def ensure_user(user_id: int, name: str = "Студент"):
    with db_lock, extra_db() as conn:
        conn.execute(
            "INSERT OR IGNORE INTO users(user_id,name,created_at) VALUES (?,?,?)",
            (user_id, name, now_iso())
        )

def audit(actor: str, action: str, details: str):
    with db_lock, extra_db() as conn:
        conn.execute(
            "INSERT INTO audit_log(actor,action,details,created_at) VALUES (?,?,?,?)",
            (actor, action, details, now_iso())
        )

def add_notification(user_id: int, title: str, message: str):
    with db_lock, extra_db() as conn:
        conn.execute(
            "INSERT INTO notifications(user_id,title,message,created_at) VALUES (?,?,?,?)",
            (user_id, title, message, now_iso())
        )

def loyalty_level(points: int) -> str:
    if points >= 1000:
        return "LEGEND"
    if points >= 500:
        return "PRO"
    if points >= 200:
        return "PLUS"
    return "NEW"

def update_loyalty(user_id: int, delta: int):
    ensure_user(user_id)
    with db_lock, extra_db() as conn:
        row = conn.execute("SELECT points FROM users WHERE user_id=?", (user_id,)).fetchone()
        points = max(0, int(row["points"]) + delta)
        conn.execute(
            "UPDATE users SET points=?, level=? WHERE user_id=?",
            (points, loyalty_level(points), user_id)
        )
        return points


def register_cashback_progress(user_id: int, has_hot_food: bool) -> dict:
    """«Студенческий кэшбэк»: каждый 5-й полноценный обед даёт бесплатный кофе."""
    ensure_user(user_id)
    with db_lock, extra_db() as conn:
        conn.execute(
            "INSERT OR IGNORE INTO cashback_progress(user_id, updated_at) VALUES (?, ?)",
            (user_id, now_iso()),
        )
        row = conn.execute(
            "SELECT hot_lunches_count, free_coffees_earned, free_coffees_used "
            "FROM cashback_progress WHERE user_id=?", (user_id,)
        ).fetchone()
        count = int(row["hot_lunches_count"])
        earned = int(row["free_coffees_earned"])
        just_earned = False
        if has_hot_food:
            count += 1
            if count % CASHBACK_LUNCHES_TARGET == 0:
                earned += 1
                just_earned = True
        conn.execute(
            "UPDATE cashback_progress SET hot_lunches_count=?, free_coffees_earned=?, updated_at=? WHERE user_id=?",
            (count, earned, now_iso(), user_id),
        )
    if just_earned:
        add_notification(
            user_id, "🎁 Бесплатный кофе разблокирован!",
            f"Вы оформили {CASHBACK_LUNCHES_TARGET}-й полноценный обед через UniFood — "
            f"в приложении вас ждёт бесплатный кофе. Заберите его на стойке выдачи."
        )
    return {
        "hot_lunches_count": count,
        "free_coffees_earned": earned,
        "remaining_to_next_coffee": CASHBACK_LUNCHES_TARGET - (count % CASHBACK_LUNCHES_TARGET) if count % CASHBACK_LUNCHES_TARGET else 0,
        "just_earned": just_earned,
    }


def get_cashback_status(user_id: int) -> dict:
    ensure_user(user_id)
    with db_lock, extra_db() as conn:
        row = conn.execute(
            "SELECT hot_lunches_count, free_coffees_earned, free_coffees_used "
            "FROM cashback_progress WHERE user_id=?", (user_id,)
        ).fetchone()
    if not row:
        return {
            "user_id": user_id, "hot_lunches_count": 0, "free_coffees_earned": 0,
            "free_coffees_available": 0, "remaining_to_next_coffee": CASHBACK_LUNCHES_TARGET,
            "target": CASHBACK_LUNCHES_TARGET,
        }
    count = int(row["hot_lunches_count"])
    earned = int(row["free_coffees_earned"])
    used = int(row["free_coffees_used"])
    remainder = count % CASHBACK_LUNCHES_TARGET
    return {
        "user_id": user_id,
        "hot_lunches_count": count,
        "free_coffees_earned": earned,
        "free_coffees_available": max(0, earned - used),
        "remaining_to_next_coffee": CASHBACK_LUNCHES_TARGET - remainder if remainder else CASHBACK_LUNCHES_TARGET,
        "target": CASHBACK_LUNCHES_TARGET,
    }


def require_admin(token: str) -> None:
    if not secrets.compare_digest(token, ADMIN_TOKEN):
        raise HTTPException(status_code=403, detail="Недостаточно прав")


def require_api_token(token: Optional[str]) -> None:
    if API_TOKEN and token != API_TOKEN:
        raise HTTPException(status_code=401, detail="Неверный API token")


def validate_pickup_time(pickup_time: str) -> str:
    value = pickup_time.strip()
    allowed = {x.split(" ", 1)[0] for x in PICKUP_SLOTS}
    if value not in allowed and value not in PICKUP_SLOTS:
        raise HTTPException(400, "Выберите доступное время выдачи из списка pickup_slots")
    return value


def recommendation_score(item: MenuItem, favorite_ids: set[int], query_ids: set[int]) -> float:
    score = 0.0
    if item.id in favorite_ids:
        score += 10
    if item.id in query_ids:
        score += 5
    if item.stock > 0:
        score += 3
    if item.is_hot:
        score += 0.5
    score += max(0, 100 - item.price_rub) / 100
    return score


def menu_signature(menu: List[MenuItem]) -> str:
    raw = json.dumps([m.model_dump() for m in menu], ensure_ascii=False, sort_keys=True)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]

_RATE_BUCKETS: dict[str, list[float]] = {}
_RATE_LOCK = threading.Lock()

def client_key(request: Request) -> str:
    return (request.headers.get("X-Forwarded-For") or request.client.host or "local").split(",")[0].strip()

def rate_limit(request: Request, scope: str, limit: int, window: int = 60) -> None:
    now = time.monotonic()
    key = f"{scope}:{client_key(request)}"
    with _RATE_LOCK:
        values = [x for x in _RATE_BUCKETS.get(key, []) if now - x < window]
        if len(values) >= limit:
            raise HTTPException(429, "Слишком много запросов. Попробуйте позже.")
        values.append(now)
        _RATE_BUCKETS[key] = values
        if len(_RATE_BUCKETS) > 2000:
            for k in list(_RATE_BUCKETS)[:500]:
                _RATE_BUCKETS.pop(k, None)

def security_headers(response: Response, request_id: str) -> Response:
    response.headers["X-Request-ID"] = request_id
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "SAMEORIGIN"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    response.headers["Permissions-Policy"] = "camera=(), microphone=(), geolocation=()"
    response.headers["Cache-Control"] = "no-store"
    return response

app = FastAPI(
    title=APP_TITLE,
    version=APP_VERSION,
    description="NETI_Food 7.2 MEGA — цифровая столовая НГТУ НЭТИ: предзаказ, аналитика, лояльность и умный постамат.",
    docs_url="/docs",
    redoc_url="/redoc",
    lifespan=lifespan,
)

@app.middleware("http")
async def request_guard(request: Request, call_next):
    request_id = secrets.token_hex(8)
    started = time.perf_counter()
    response = await call_next(request)
    response = security_headers(response, request_id)
    response.headers["Server-Timing"] = f"app;dur={(time.perf_counter()-started)*1000:.1f}"
    return response

app.add_middleware(
    CORSMiddleware,
    allow_origins=[
        x.strip() for x in os.getenv(
            "NETI_FOOD_CORS_ORIGINS",
            "http://127.0.0.1:8000,http://localhost:8000"
        ).split(",") if x.strip()
    ],
    allow_credentials=True,
    allow_methods=["GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS"],
    allow_headers=["Content-Type", "Authorization", "X-API-Token", "Idempotency-Key", "X-Requested-With"],
)
app.add_middleware(GZipMiddleware, minimum_size=900)

@app.get("/api/health")
def health():
    with db_lock, db() as conn:
        orders = conn.execute("SELECT COUNT(*) AS c FROM orders").fetchone()["c"]
    return {
        "status": "ok",
        "version": APP_VERSION,
        "database": str(DB_PATH),
        "orders": orders,
        "hardware": "serial" if serial else "simulation",
        "timestamp": now_iso(),
    }


@app.get("/api/config")
def config():
    return {
        "app_name": APP_TITLE,
        "version": APP_VERSION,
        "discount_percent": CAMPUS_DISCOUNT * 100,
        "pickup_slots": PICKUP_SLOTS,
        "locker_count": LOCKER_COUNT,
        "hardware_port": HARDWARE_PORT if serial else "simulation",
    }


@app.get("/api/menu", response_model=List[MenuItem])
def get_menu(
    category: str = "all",
    search: str = "",
    is_vegan: Optional[bool] = None,
    is_lactose_free: Optional[bool] = None,
    only_available: bool = False,
    max_price: Optional[float] = Query(None, ge=0),
):
    results = menu_with_stock()

    if category != "all":
        results = [i for i in results if i.category.value == category]

    query = " ".join(search.lower().split())
    if query:
        results = [
            i for i in results
            if query in i.name.lower()
            or query in i.description.lower()
            or any(query in a.lower() for a in i.allergens)
        ]

    if is_vegan is True:
        results = [i for i in results if i.is_vegan]

    if is_lactose_free is True:
        results = [i for i in results if i.is_lactose_free]

    if only_available:
        results = [i for i in results if i.stock > 0]

    if max_price is not None:
        results = [i for i in results if i.price_rub <= max_price]

    return results


@app.get("/api/menu/meta")
def menu_meta():
    menu = menu_with_stock()
    categories = {}
    for category in FoodCategory:
        categories[category.value] = sum(
            1 for item in menu if item.category == category
        )
    return {
        "items": len(menu),
        "available": sum(1 for item in menu if item.stock > 0),
        "categories": categories,
        "pickup_slots": PICKUP_SLOTS,
    }


@app.get("/api/menu/{item_id}", response_model=MenuItem)
def menu_item(item_id: int):
    return get_menu_item(item_id)


@app.post("/api/orders/create", response_model=Order, status_code=201)
def create_order(payload: OrderCreate, request: Request):
    user = auth_user(request)
    idem_key = request.headers.get("Idempotency-Key", "").strip()
    if idem_key:
        if len(idem_key) > 100 or not re.fullmatch(r"[A-Za-z0-9._:-]+", idem_key):
            raise HTTPException(400, "Некорректный Idempotency-Key")
    rate_limit(request, "order-create", 30, 60)
    if int(user["user_id"]) != payload.user_id:
        raise HTTPException(403, "Нельзя создать заказ от имени другого пользователя")

    if idem_key:
        with db_lock, extra_db() as conn:
            previous = conn.execute(
                "SELECT order_id FROM idempotency_keys WHERE user_id=? AND idem_key=?",
                (payload.user_id, idem_key)
            ).fetchone()
        if previous:
            return get_order(int(previous["order_id"]))

    if not payload.items:
        raise HTTPException(400, "Корзина не может быть пустой")

    if payload.pickup_time not in PICKUP_SLOTS:
        raise HTTPException(400, "Выберите доступное время выдачи")

    # Склеиваем дублирующиеся позиции до проверки склада.
    merged: dict[int, int] = {}
    for cart_item in payload.items:
        merged[cart_item.item_id] = (
            merged.get(cart_item.item_id, 0) + cart_item.quantity
        )

    if len(merged) > MAX_ORDER_ITEMS or sum(merged.values()) > MAX_TOTAL_QUANTITY:
        raise HTTPException(400, "Слишком большой заказ")

    with db_lock, db() as conn:
        total_before = 0.0
        total_calories = 0.0
        allergens: set[str] = set()
        ordered_names: list[str] = []
        has_hot_food = False
        order_items = []

        # Важный момент: итоговая цена всегда рассчитывается на сервере.
        for item_id, quantity in merged.items():
            item = MENU_BY_ID.get(item_id)
            if not item:
                raise HTTPException(404, f"Блюдо #{item_id} не найдено")

            row = conn.execute(
                "SELECT stock FROM menu_stock WHERE item_id = ?",
                (item_id,),
            ).fetchone()
            stock = row["stock"] if row else 0

            if stock < quantity:
                raise HTTPException(
                    400,
                    f"Недостаточно «{item.name}». Доступно: {stock}",
                )

            conn.execute(
                "UPDATE menu_stock SET stock = stock - ? WHERE item_id = ?",
                (quantity, item_id),
            )

            line_total = item.price_rub * quantity
            total_before += line_total
            total_calories += item.kbju.calories * quantity
            allergens.update(item.allergens)
            ordered_names.append(f"{item.name} ×{quantity}")
            has_hot_food = has_hot_food or item.is_hot
            order_items.append({
                "item_id": item_id,
                "quantity": quantity,
                "name": item.name,
                "unit_price": item.price_rub,
            })

        discount = round(total_before * CAMPUS_DISCOUNT, 2)
        total_price = round(total_before - discount, 2)
        created = now_iso()

        row = conn.execute(
            "SELECT COALESCE(MAX(order_id), 300) + 1 AS next_id FROM orders"
        ).fetchone()
        order_id = int(row["next_id"])

        qr = generate_qr(
            f"UNIFOOD|ORDER:{order_id}|USER:{payload.user_id}"
        )

        conn.execute(
            """
            INSERT INTO orders(
                order_id, user_id, pickup_time, items_json, items_summary,
                has_hot_food, total_price, total_before_discount,
                discount_amount, total_calories, allergens_json,
                status, cell_number, qr_code, created_at, updated_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                order_id,
                payload.user_id,
                payload.pickup_time,
                json.dumps(order_items, ensure_ascii=False),
                ", ".join(ordered_names),
                int(has_hot_food),
                total_price,
                round(total_before, 2),
                discount,
                total_calories,
                json.dumps(sorted(allergens), ensure_ascii=False),
                OrderStatus.PAID.value,
                None,
                qr,
                created,
                created,
            ),
        )
        if idem_key:
            with db_lock, extra_db() as extra_conn:
                extra_conn.execute(
                    "INSERT INTO idempotency_keys(user_id, idem_key, order_id, created_at) VALUES (?,?,?,?)",
                    (payload.user_id, idem_key, order_id, created)
                )

    add_event(
        order_id,
        OrderStatus.PAID.value,
        "Заказ оплачен",
        "Заказ принят системой и ожидает приготовления.",
    )
    register_cashback_progress(payload.user_id, has_hot_food)
    return get_order(order_id)


@app.get("/api/orders", response_model=List[Order])
def get_orders(
    user_id: Optional[int] = Query(None, ge=1),
    status_filter: Optional[OrderStatus] = None,
    limit: int = Query(100, ge=1, le=500),
):
    with db_lock, db() as conn:
        sql = "SELECT * FROM orders WHERE 1=1"
        params: list = []

        if user_id is not None:
            sql += " AND user_id = ?"
            params.append(user_id)

        if status_filter:
            sql += " AND status = ?"
            params.append(status_filter.value)

        sql += " ORDER BY order_id DESC LIMIT ?"
        params.append(limit)

        rows = conn.execute(sql, params).fetchall()

    return [row_to_order(row) for row in rows]


@app.get("/api/orders/active", response_model=Optional[Order])
def active_order(request: Request):
    """Return only the current user's non-completed order.

    The browser must never infer ownership of an order from localStorage.
    This endpoint is the source of truth after refresh/reopen.
    """
    user = auth_user(request)
    with db_lock, db() as conn:
        row = conn.execute(
            """SELECT * FROM orders
               WHERE user_id = ? AND status IN (?, ?, ?)
               ORDER BY order_id DESC LIMIT 1""",
            (int(user["user_id"]), OrderStatus.PAID.value, OrderStatus.COOKING.value, OrderStatus.READY.value),
        ).fetchone()
    return row_to_order(row) if row else None


@app.get("/api/orders/{order_id}", response_model=Order)
def order_details(order_id: int):
    return get_order(order_id)


@app.get("/api/orders/{order_id}/events", response_model=List[OrderEvent])
def order_events(order_id: int):
    order = get_order(order_id)
    with db_lock, db() as conn:
        rows = conn.execute(
            """
            SELECT * FROM order_events
            WHERE order_id = ?
            ORDER BY id ASC
            """,
            (order.order_id,),
        ).fetchall()

    order_flow = [
        OrderStatus.PAID.value,
        OrderStatus.COOKING.value,
        OrderStatus.READY.value,
        OrderStatus.COMPLETED.value,
    ]
    current_index = order_flow.index(order.status.value)

    return [
        OrderEvent(
            status=row["status"],
            title=row["title"],
            description=row["description"],
            created_at=row["created_at"],
            done=order_flow.index(row["status"]) <= current_index,
        )
        for row in rows
    ]


@app.post("/api/orders/{order_id}/status/cooking", response_model=Order)
def set_order_cooking(order_id: int):
    return update_order_status(order_id, OrderStatus.COOKING)


@app.post("/api/orders/{order_id}/ready", response_model=Order)
async def set_order_ready(
    order_id: int,
    background_tasks: BackgroundTasks,
    cell_number: Optional[int] = Query(None, ge=1, le=LOCKER_COUNT),
):
    order = get_order(order_id)

    if order.status != OrderStatus.COOKING:
        raise HTTPException(
            400, "В ячейку можно поместить только заказ из статуса COOKING"
        )

    # Если ячейка не указана — берём первую свободную.
    if cell_number is None:
        cells = free_cells()
        if not cells:
            raise HTTPException(409, "Все ячейки постамата заняты")
        cell_number = cells[0]

    occupied = occupied_cells()
    existing = occupied.get(cell_number)
    if existing and existing.order_id != order_id:
        raise HTTPException(
            409,
            f"Ячейка #{cell_number} уже занята заказом #{existing.order_id}",
        )

    updated = update_order_status(
        order_id,
        OrderStatus.READY,
        cell_number=cell_number,
    )
    background_tasks.add_task(
        send_to_hardware_async, cell_number, "ON"
    )
    return updated


@app.post("/api/orders/{order_id}/pickup", response_model=Order)
async def pickup_order(
    order_id: int,
    background_tasks: BackgroundTasks,
):
    order = get_order(order_id)

    if order.status != OrderStatus.READY:
        raise HTTPException(400, "Заказ ещё не готов к выдаче")

    cell = order.cell_number
    updated = update_order_status(
        order_id,
        OrderStatus.COMPLETED,
        cell_number=None,
    )

    if cell:
        background_tasks.add_task(
            send_to_hardware_async, cell, "OFF"
        )

    return updated


@app.get("/api/lockers")
def locker_status():
    occupied = occupied_cells()
    cells = []

    for number in range(1, LOCKER_COUNT + 1):
        order = occupied.get(number)
        cells.append({
            "cell_number": number,
            "temperature": "+60°C" if number <= 4 else "+4°C",
            "mode": "hot" if number <= 4 else "cool",
            "occupied": order is not None,
            "order_id": order.order_id if order else None,
            "user_id": order.user_id if order else None,
        })

    return {
        "total": LOCKER_COUNT,
        "free": len(free_cells()),
        "occupied": len(occupied),
        "cells": cells,
    }


@app.get("/api/stats")
def kitchen_stats():
    with db_lock, db() as conn:
        rows = conn.execute(
            """
            SELECT status, COUNT(*) AS count
            FROM orders
            GROUP BY status
            """
        ).fetchall()

        total_today = conn.execute(
            """
            SELECT COUNT(*) AS count
            FROM orders
            WHERE date(created_at, 'localtime') = date('now', 'localtime')
            """
        ).fetchone()["count"]

        revenue_today = conn.execute(
            """
            SELECT COALESCE(SUM(total_price), 0) AS total
            FROM orders
            WHERE date(created_at, 'localtime') = date('now', 'localtime')
            """
        ).fetchone()["total"]

    status_counts = {status.value: 0 for status in OrderStatus}
    for row in rows:
        status_counts[row["status"]] = row["count"]

    return {
        "today_orders": total_today,
        "today_revenue": round(revenue_today, 2),
        "status_counts": status_counts,
        "free_lockers": len(free_cells()),
    }


@app.post("/api/admin/restock")
def restock(
    item_id: int,
    amount: int = Query(..., ge=1, le=1000),
):
    item = get_menu_item(item_id)

    with db_lock, db() as conn:
        conn.execute(
            """
            INSERT INTO menu_stock(item_id, stock)
            VALUES (?, ?)
            ON CONFLICT(item_id)
            DO UPDATE SET stock = stock + excluded.stock
            """,
            (item_id, amount),
        )
        row = conn.execute(
            "SELECT stock FROM menu_stock WHERE item_id = ?",
            (item_id,),
        ).fetchone()

    return {
        "status": "success",
        "item_id": item_id,
        "item": item.name,
        "stock": row["stock"],
    }

HTML = r"""
<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#be123c">
<meta name="color-scheme" content="light">
<meta name="apple-mobile-web-app-title" content="NETI Food">
<link rel="apple-touch-icon" sizes="180x180" href="/icon-180.png">
<link rel="icon" type="image/png" sizes="192x192" href="/icon-192.png">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="format-detection" content="telephone=no">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<link rel="manifest" href="/manifest.webmanifest">
<meta name="application-name" content="NETI Food"><title>NETI_Food 7.2 MEGA — НГТУ НЭТИ</title>
<script src="https://cdn.tailwindcss.com"></script>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">
<style>
:root{--red:#be123c;--dark:#881337;--teal:#0f766e;--ink:#0f172a;--muted:#64748b;--surface:#ffffff;--bg:#f4f6f8}
*{box-sizing:border-box}
body{font-family:Inter,system-ui,sans-serif;background:#f8fafc;color:#0f172a}
button,input,select{font:inherit}
.no-scrollbar::-webkit-scrollbar{display:none}
.no-scrollbar{scrollbar-width:none}
.glass{backdrop-filter:blur(16px);-webkit-backdrop-filter:blur(16px)}
.card{transition:transform .18s,box-shadow .18s}
.card:hover{transform:translateY(-2px);box-shadow:0 12px 30px rgba(15,23,42,.09)}
.skeleton{background:linear-gradient(90deg,#e2e8f0 25%,#f8fafc 50%,#e2e8f0 75%);background-size:200% 100%;animation:sh 1.3s infinite}
@keyframes sh{to{background-position:-200% 0}}
.fade{animation:fade .22s ease-out}
@keyframes fade{from{opacity:0;transform:translateY(5px)}to{opacity:1;transform:none}}
.pulse-dot{animation:pulseDot 1.5s infinite}
@keyframes pulseDot{50%{opacity:.35}}
.led-hot{box-shadow:0 0 0 1px #fb7185,0 0 22px rgba(244,63,94,.55)}
.led-cool{box-shadow:0 0 0 1px #60a5fa,0 0 22px rgba(59,130,246,.45)}
.modal-bg{background:rgba(15,23,42,.68);backdrop-filter:blur(8px)}
.safe-bottom{padding-bottom:env(safe-area-inset-bottom)}
html,body{min-height:100%;-webkit-text-size-adjust:100%;text-rendering:optimizeLegibility}
button,a,input,select{touch-action:manipulation}
button{cursor:pointer;-webkit-tap-highlight-color:transparent}
img{display:block;max-width:100%}
input,select,textarea{min-width:0;outline:none}
@media (prefers-reduced-motion:reduce){*,*::before,*::after{animation-duration:.01ms!important;animation-iteration-count:1!important;scroll-behavior:auto!important;transition-duration:.01ms!important}}

.mobile-nav{padding-bottom:max(8px,env(safe-area-inset-bottom))}
.touch-target{min-width:44px;min-height:44px}
.snap-x{scroll-snap-type:x mandatory}.snap-item{scroll-snap-align:start}
.account-chip{background:linear-gradient(135deg,#e11d48,#be123c)!important;color:#fff!important;box-shadow:0 8px 20px rgba(225,29,72,.18)}
@media (max-width:640px){
 body{font-size:14px;overscroll-behavior-y:none;background:var(--bg)}
 main{padding-top:10px!important}
 #menu{grid-template-columns:1fr!important;gap:10px!important}
 .card{border-radius:24px!important;border:0!important;box-shadow:0 5px 22px rgba(15,23,42,.07)!important;overflow:hidden;background:#fff}
 .card:hover{transform:none;box-shadow:0 5px 22px rgba(15,23,42,.07)!important}
 .card .dish-photo{height:185px!important}
 .mobile-sheet{border-radius:28px 28px 0 0!important;max-height:94vh!important}
 #categories{margin-right:-16px;padding-right:16px;padding-bottom:4px}
 #categories button{height:42px;border-radius:14px;padding:0 15px;box-shadow:0 2px 8px rgba(15,23,42,.04)}
 .filter{white-space:nowrap;border-radius:14px!important}
 #sort{width:100%;height:46px;border-radius:15px}
 .mobile-nav{background:rgba(255,255,255,.92)!important;border-top:1px solid rgba(148,163,184,.18)!important;box-shadow:0 -12px 30px rgba(15,23,42,.10)!important}
 .mobile-nav button{min-height:58px;color:#64748b;position:relative}
 .mobile-nav button:first-child:before{content:'';position:absolute;top:2px;left:24%;right:24%;height:3px;border-radius:99px;background:#be123c;opacity:.0}
 .mobile-nav button:active{transform:scale(.96)}
 .mobile-hero{margin:0 -16px 14px;border-radius:0 0 28px 28px;padding:18px 16px 20px;background:linear-gradient(145deg,#be123c 0%,#9f1239 48%,#4c0519 100%);color:white;box-shadow:0 14px 32px rgba(136,19,55,.20)}
 .mobile-hero .balance{background:rgba(255,255,255,.13);border:1px solid rgba(255,255,255,.15);backdrop-filter:blur(12px);border-radius:22px;padding:14px}
 .mobile-quick{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-top:10px}
 .mobile-quick button{min-height:66px;border-radius:18px;background:rgba(255,255,255,.12);border:1px solid rgba(255,255,255,.13);font-size:11px;font-weight:800}
 .mobile-quick button:active{transform:scale(.97)}
 .section-card{border:0!important;box-shadow:0 5px 22px rgba(15,23,42,.06)!important}
 .smart-card{border:0!important;background:linear-gradient(145deg,#fff,#f8fafc)!important;box-shadow:0 5px 22px rgba(15,23,42,.06)!important}
 .snap-item{width:205px!important;border:0!important;box-shadow:0 4px 16px rgba(15,23,42,.07)}
}
@media (min-width:641px){.mobile-hero{display:none!important}}
.mobile-hero{display:none}
@media (max-width:640px){.mobile-hero{display:block}}
@media (min-width:641px){.mobile-nav{display:none!important}}

:root{--ngtu-red:#be123c;--ngtu-red2:#9f1239;--ngtu-navy:#111827;--ngtu-paper:#f8fafc;--ngtu-line:#e5e7eb}
::selection{background:#fecdd3;color:#881337}
html{scroll-behavior:smooth}
body{background:radial-gradient(circle at 0 0,rgba(190,18,60,.045),transparent 28rem),#f8fafc}
body:before{content:"";position:fixed;inset:0;pointer-events:none;opacity:.035;background-image:linear-gradient(rgba(15,23,42,.8) 1px,transparent 1px),linear-gradient(90deg,rgba(15,23,42,.8) 1px,transparent 1px);background-size:32px 32px;z-index:-1}
.ngtu-ribbon{height:4px;background:linear-gradient(90deg,#881337 0%,#be123c 48%,#e11d48 70%,#0f766e 100%)}
.ngtu-brandmark{position:relative;overflow:hidden}
.ngtu-brandmark:after{content:"";position:absolute;width:70px;height:70px;border:1px solid rgba(255,255,255,.18);border-radius:50%;right:-32px;top:-30px}
.header-glow{box-shadow:0 12px 40px rgba(136,19,55,.18)}
.kpi-strip{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:10px}
.kpi-tile{background:rgba(255,255,255,.82);border:1px solid rgba(148,163,184,.18);border-radius:20px;padding:14px;box-shadow:0 5px 20px rgba(15,23,42,.045)}
.command-kbd{font-size:10px;border:1px solid rgba(148,163,184,.3);border-bottom-width:2px;border-radius:7px;padding:2px 6px;background:#fff}
.status-online{display:inline-flex;align-items:center;gap:6px}
.status-online:before{content:"";width:7px;height:7px;border-radius:50%;background:#10b981;box-shadow:0 0 0 4px rgba(16,185,129,.12)}
.dish-photo{background:linear-gradient(135deg,#f1f5f9,#fff)}
.price-chip{background:#fff1f2;color:#9f1239;border:1px solid #fecdd3}
.btn-ngtu{background:linear-gradient(135deg,#be123c,#881337);color:#fff;box-shadow:0 8px 18px rgba(190,18,60,.18)}
.btn-ngtu:hover{filter:brightness(1.04)}
.mobile-nav{backdrop-filter:blur(18px);-webkit-backdrop-filter:blur(18px)}
@media(max-width:640px){.kpi-strip{grid-template-columns:repeat(2,1fr)}.ngtu-desktop-only{display:none!important}}
@media(prefers-reduced-motion:reduce){*,*::before,*::after{scroll-behavior:auto!important;animation:none!important;transition:none!important}}

.app-splash{position:fixed;inset:0;z-index:9999;display:grid;place-items:center;overflow:hidden;background:
 radial-gradient(circle at 20% 20%,rgba(244,63,94,.25),transparent 30%),
 radial-gradient(circle at 80% 80%,rgba(16,185,129,.12),transparent 28%),#080b14;color:#fff;
 transition:opacity .55s ease,visibility .55s ease}
.app-splash.hide{opacity:0;visibility:hidden;pointer-events:none}
.splash-card{text-align:center;position:relative;z-index:2;padding:28px 32px}
.splash-logo{width:76px;height:76px;margin:0 auto 16px;display:grid;place-items:center;border-radius:26px;
 background:linear-gradient(145deg,#e11d48,#881337);font-size:38px;box-shadow:0 18px 50px rgba(225,29,72,.35);animation:splashPop .8s cubic-bezier(.2,.9,.2,1)}
.splash-title{font-size:36px;font-weight:900;letter-spacing:-1.8px}
.splash-title span{color:#34d399}
.splash-subtitle{font-size:10px;font-weight:800;letter-spacing:.22em;color:#cbd5e1;margin-top:7px}
.splash-progress{width:min(280px,72vw);height:4px;background:#1e293b;border-radius:999px;overflow:hidden;margin:24px auto 12px}
.splash-progress span{display:block;height:100%;width:42%;border-radius:999px;background:linear-gradient(90deg,#e11d48,#34d399);animation:splashLoad 1.5s ease-in-out infinite}
.splash-status{font-size:11px;color:#94a3b8;font-weight:700}
.splash-orbit{position:absolute;width:58vmin;height:58vmin;border:1px solid rgba(255,255,255,.06);border-radius:50%;animation:orbit 18s linear infinite}
@keyframes splashPop{from{opacity:0;transform:scale(.7) translateY(18px)}to{opacity:1;transform:none}}
@keyframes splashLoad{0%{transform:translateX(-120%)}100%{transform:translateX(340%)}}
@keyframes orbit{to{transform:rotate(360deg)}}
.pressable{transition:transform .12s ease}.pressable:active{transform:scale(.97)}
.live-chip{display:inline-flex;align-items:center;gap:7px;padding:7px 10px;border-radius:999px;background:rgba(255,255,255,.1);border:1px solid rgba(255,255,255,.12);font-size:10px;font-weight:800}
.live-chip i{width:7px;height:7px;border-radius:50%;background:#34d399;box-shadow:0 0 0 5px rgba(52,211,153,.12)}
@media(prefers-reduced-motion:reduce){.app-splash *{animation:none!important}}
body{padding-bottom:env(safe-area-inset-bottom)}
.safe-top{padding-top:env(safe-area-inset-top)}
@supports (-webkit-touch-callout:none){button,input,select{font-size:16px}}

html{min-height:100%;background:#f8fafc}
body{min-height:100dvh;overflow-x:hidden}
main{width:min(100% - 32px, 1440px)!important;max-width:1440px!important}
header>div{width:min(100% - 32px, 1440px)!important;max-width:1440px!important}
#menu{grid-template-columns:repeat(3,minmax(0,1fr))}
@media (min-width:1280px){
  #menu{grid-template-columns:repeat(4,minmax(0,1fr))}
  main{padding-top:28px!important}
  .dish-photo{height:210px!important}
}
@media (min-width:641px) and (max-width:1024px){
  #menu{grid-template-columns:repeat(2,minmax(0,1fr))}
}
@media (max-width:768px){
  main{width:100%!important;max-width:none!important;padding-left:16px!important;padding-right:16px!important;padding-bottom:calc(8rem + env(safe-area-inset-bottom))!important}
  header>div{width:100%!important;max-width:none!important;padding-left:12px!important;padding-right:12px!important}
  header{position:sticky!important}
  header .ngtu-brandmark{width:42px;height:42px}
  header .text-xl{font-size:18px}
  #search{font-size:16px!important;min-height:48px}
  #accountBtn{padding-left:12px!important;padding-right:12px!important}
  body.pwa-installed #installBtn{display:none!important}
  .modal-bg{padding:0!important}
  .modal-bg>div{max-height:96dvh!important}
}
@media (max-width:640px){
  #menu{grid-template-columns:1fr!important}
  .dish-photo{height:185px!important}
  .mobile-nav{padding-bottom:max(10px,env(safe-area-inset-bottom));min-height:72px}
  .mobile-nav button{min-height:60px}
}
@media (min-width:769px){
  #installBtn{display:none!important}
}
@media (hover:none){
  .card:hover{transform:none!important}
}
@supports (height:100dvh){
  .app-splash{height:100dvh}
}
</style>
</head>
<body class="min-h-screen">
<div id="appSplash" class="app-splash" aria-label="NETI Food">
  <div class="splash-orbit"></div>
  <div class="splash-card">
    <div class="splash-logo">🍎</div>
    <div class="splash-title">NETI<span>_Food</span></div>
    <div class="splash-subtitle">ЦИФРОВАЯ СТОЛОВАЯ • НГТУ НЭТИ</div>
    <div class="splash-progress"><span></span></div>
    <div id="splashStatus" class="splash-status">Подключаем сервисы…</div>
  </div>
</div>
<div class="ngtu-ribbon"></div>

<div id="commandPalette" class="hidden fixed inset-0 z-[120] bg-slate-950/60 backdrop-blur-sm p-4 items-start justify-center">
  <div class="w-full max-w-xl mt-[10vh] bg-white rounded-[28px] shadow-2xl overflow-hidden">
    <div class="p-4 border-b flex items-center gap-3">
      <span class="text-xl">⌕</span><input id="commandInput" autofocus class="flex-1 outline-none font-semibold" placeholder="Найти блюдо или действие…">
      <button onclick="closeCommandPalette()" class="text-xs text-slate-400">Esc</button>
    </div>
    <div id="commandResults" class="p-2 max-h-[55vh] overflow-auto"></div>
  </div>
</div>

<div id="toast" class="fixed top-4 right-4 z-[100] w-[min(360px,calc(100vw-2rem))] space-y-2"></div>

<header class="sticky top-0 z-40 text-white shadow-xl" style="background:linear-gradient(135deg,#be123c,#881337)">
  <div class="max-w-6xl mx-auto px-4 py-4">
    <div class="flex items-center justify-between gap-3">
      <div class="flex items-center gap-3 min-w-0">
        <div class="ngtu-brandmark w-11 h-11 rounded-2xl bg-white/15 border border-white/20 flex items-center justify-center text-2xl">🍎</div>
        <div class="min-w-0">
          <div class="font-black text-xl tracking-tight">NETI_Food <span class="text-emerald-300">7.2</span></div>
          <div class="text-[10px] text-rose-100 truncate">НГТУ НЭТИ • «Под яблоком Ньютона»</div>
        </div>
      </div>
      <div class="hidden sm:flex items-center gap-2 text-xs font-bold">
        <span class="px-3 py-1.5 rounded-full bg-white/10 border border-white/10">Кампус −5%</span>
        <button onclick="openOrders()" class="px-3 py-1.5 rounded-full bg-white text-rose-700">Мои заказы</button>
      </div>
    </div>

    <div class="mt-4 flex gap-2">
      <div class="relative flex-1">
        <span class="absolute left-3.5 top-3 text-rose-200">⌕</span>
        <input id="search" oninput="debouncedLoad()" placeholder="Поиск блюда, ингредиента или аллергена..."
          class="w-full rounded-2xl bg-black/15 border border-white/10 py-3 pl-10 pr-10 text-sm placeholder:text-rose-200 outline-none focus:ring-2 focus:ring-emerald-300">
        <button id="clear" onclick="clearSearch()" class="hidden absolute right-3 top-2.5 text-xl text-rose-200">×</button>
      </div>
      <button id="accountBtn" onclick="openAccount()" class="account-chip touch-target shrink-0 rounded-2xl bg-rose-600 text-white px-4 text-xs font-black shadow-sm active:scale-95 transition">NETI ID</button>
      <button id="installBtn" onclick="installNETIFood()" class="hidden sm:hidden touch-target w-12 shrink-0 rounded-2xl bg-emerald-400 text-slate-950 font-black shadow-lg" aria-label="Установить NETI Food" title="Установить как приложение">＋</button>
    <button onclick="openCart()" class="relative w-12 rounded-2xl bg-white text-rose-700 font-black shadow-lg">
        🛒
        <span id="badge" class="absolute -top-1 -right-1 min-w-5 h-5 px-1 rounded-full bg-emerald-400 text-[10px] text-slate-900 flex items-center justify-center">0</span>
      </button>
    </div>
    <div class="hidden md:flex items-center justify-between mt-3 text-[10px] font-bold text-rose-100">
      <div class="flex items-center gap-4">
        <span class="status-online">Система онлайн</span><span id="networkChip" class="live-chip"><i></i><b>ONLINE</b></span>
        <span>Предзаказ • Постамат • Лояльность</span>
      </div>
      <button onclick="openCommandPalette()" class="flex items-center gap-2 opacity-90 hover:opacity-100">
        Быстрый поиск <span class="command-kbd">Ctrl K</span>
      </button>
    </div>
  </div>
</header>

<main class="max-w-6xl mx-auto px-4 py-5 pb-32">
  <section class="mb-4 grid grid-cols-2 lg:grid-cols-4 gap-2">
    <div class="kpi-tile"><div class="text-[10px] text-slate-400 font-black uppercase tracking-wider">⚡ Быстрый заказ</div><div class="font-black mt-1">Предзаказ без очереди</div></div>
    <div class="kpi-tile"><div class="text-[10px] text-slate-400 font-black uppercase tracking-wider">🧠 Умная кухня</div><div class="font-black mt-1">Статус готовности онлайн</div></div>
    <div class="kpi-tile"><div class="text-[10px] text-slate-400 font-black uppercase tracking-wider">📦 Постамат</div><div class="font-black mt-1">Выдача по QR-коду</div></div>
    <div class="kpi-tile"><div class="text-[10px] text-slate-400 font-black uppercase tracking-wider">🎓 Campus</div><div class="font-black mt-1">−5% на заказ</div></div>
  </section>
  <section class="mobile-hero">
    <div class="flex items-center justify-between gap-3">
      <div>
        <div class="text-[10px] uppercase tracking-[.18em] text-rose-100 font-black">Добрый день 👋</div>
        <div class="text-2xl font-black tracking-tight mt-1">Что берём на обед?</div>
      </div>
      <button onclick="openOrders()" class="w-11 h-11 rounded-2xl bg-white/15 border border-white/15 text-lg">📦</button>
    </div>
    <div class="balance mt-4">
      <div class="flex items-center justify-between text-xs text-rose-100">
        <span>Кампус-бонус</span><span>−5% на заказ</span>
      </div>
      <div class="flex items-end justify-between mt-2">
        <div><div class="text-3xl font-black">NETI Pay</div><div class="text-xs text-rose-100 mt-1">Оплата и выдача в одном месте</div></div>
        <div class="text-right"><div class="text-lg font-black">0 ₽</div><div class="text-[10px] text-rose-100">бонусов</div></div>
      </div>
    </div>
    <div class="mobile-quick">
      <button onclick="scrollToMenu()">🍽️<br><span>Заказать</span></button>
      <button onclick="showFavorites()">❤️<br><span>Избранное</span></button>
      <button onclick="openCart()">🛒<br><span>Корзина</span></button>
    </div>
  </section>

  <section id="active" class="hidden mb-5"></section>

  <div class="flex flex-col lg:flex-row lg:items-end justify-between gap-3 mb-4">
    <div>
      <h2 class="text-2xl font-black tracking-tight">Меню</h2>
      <p id="menu-subtitle" class="text-sm text-slate-500 mt-1">Загрузка...</p>
    </div>
    <div class="flex gap-2">
      <select id="sort" onchange="render()" class="bg-white border border-slate-200 rounded-xl px-3 py-2 text-xs font-semibold outline-none">
        <option value="default">По умолчанию</option>
        <option value="price-asc">Сначала дешевле</option>
        <option value="price-desc">Сначала дороже</option>
        <option value="calories">По калорийности</option>
        <option value="stock">По наличию</option>
      </select>
    </div>
  </div>

  <div id="categories" class="flex gap-2 overflow-x-auto no-scrollbar pb-2 mb-3"></div>

  <div class="flex flex-wrap gap-2 mb-6">
    <button id="vegan" onclick="toggleFilter('vegan')" class="filter bg-white border border-slate-200 rounded-xl px-3 py-2 text-xs font-semibold">🌱 Веганское</button>
    <button id="lactose" onclick="toggleFilter('lactose')" class="filter bg-white border border-slate-200 rounded-xl px-3 py-2 text-xs font-semibold">🥛 Без лактозы</button>
    <button id="available" onclick="toggleFilter('available')" class="filter bg-white border border-slate-200 rounded-xl px-3 py-2 text-xs font-semibold">✓ Только в наличии</button>
    <button onclick="resetFilters()" class="bg-slate-100 text-slate-600 rounded-xl px-3 py-2 text-xs font-semibold">Сбросить</button>
  </div>

  <div id="menu" class="grid sm:grid-cols-2 lg:grid-cols-3 gap-4"></div>

  <section class="smart-card mt-7 rounded-3xl bg-white border border-slate-200 p-4 sm:p-5">
    <div class="flex items-center justify-between gap-3">
      <div><div class="text-[10px] uppercase tracking-[.18em] text-rose-600 font-black">Для тебя</div>
      <h3 class="text-lg font-black mt-1">Умный подбор на сегодня</h3>
      <p class="text-xs text-slate-500 mt-1">Учитывает наличие, избранное и быстрые перекусы.</p></div>
      <button onclick="loadSmartPicks()" class="touch-target shrink-0 rounded-xl bg-slate-100 px-3 text-xs font-black">↻</button>
    </div>
    <div id="smartPicks" class="mt-4 flex gap-3 overflow-x-auto no-scrollbar snap-x"></div>
  </section>

  <section class="mt-5 rounded-3xl overflow-hidden bg-slate-950 text-white">
    <div class="p-5 sm:p-6 flex flex-col lg:flex-row lg:items-center justify-between gap-5">
      <div><div class="text-emerald-400 text-xs font-black uppercase tracking-[.18em]">Smart Locker</div>
      <h3 class="text-xl font-black mt-1">Умный постамат 6 корпуса</h3>
      <p class="text-slate-400 text-xs mt-1">Ячейки 1–4: подогрев • 5–8: охлаждение</p></div>
      <div class="grid grid-cols-4 gap-2 min-w-0 lg:min-w-[360px]" id="lockers"></div>
    </div>
  </section>

  <section class="mt-5 rounded-3xl bg-white border border-slate-200 p-4 sm:p-5">
    <div class="flex items-center justify-between gap-3">
      <div><h3 class="font-black">👨‍🍳 Панель кухни</h3><p class="text-xs text-slate-500">Демо-интерфейс управления заказами</p></div>
      <button onclick="toggleKitchen()" class="touch-target rounded-xl bg-slate-100 px-3 text-xs font-bold">Открыть</button>
    </div>
    <div id="kitchen" class="hidden mt-5"></div>
  </section>

  <section class="mt-5 rounded-3xl bg-slate-950 text-white p-5 shadow-xl">
    <div class="flex flex-wrap items-center justify-between gap-3"><div>
      <div class="text-[10px] uppercase tracking-[.2em] text-emerald-300 font-black">NETI_Food 6.0</div>
      <h3 class="text-xl font-black mt-1">Цифровой кампус НГТУ</h3>
      <p class="text-xs text-slate-400 mt-1">Лояльность • промокоды • отзывы • уведомления • аналитика</p>
    </div><button onclick="openV5Dashboard()" class="touch-target rounded-2xl bg-emerald-400 text-slate-950 px-4 text-xs font-black">Открыть центр</button></div>
    <div id="v5Quick" class="grid grid-cols-2 sm:grid-cols-4 gap-2 mt-4"></div>
  </section>

  <nav class="mobile-nav hidden fixed bottom-0 inset-x-0 z-[45] bg-white/95 glass border-t border-slate-200 grid-cols-4 gap-1 px-2 pt-2 shadow-[0_-8px_30px_rgba(15,23,42,.10)] safe-bottom">
    <button onclick="scrollToMenu()" class="touch-target rounded-xl text-xs font-black text-slate-600">🍽️<span class="block mt-0.5">Меню</span></button>
    <button onclick="showFavorites()" class="touch-target rounded-xl text-xs font-black text-slate-600">❤️<span class="block mt-0.5">Избранное</span></button>
    <button onclick="openOrders()" class="touch-target rounded-xl text-xs font-black text-slate-600">📦<span class="block mt-0.5">Заказы</span></button>
    <button onclick="openCart()" class="touch-target rounded-xl text-xs font-black text-rose-700">🛒<span class="block mt-0.5">Корзина</span></button>
  </nav>

</main>

<div id="cartModal" class="hidden fixed inset-0 z-50 modal-bg p-3 sm:p-6 items-end sm:items-center justify-center">
 <div class="mobile-sheet bg-white w-full max-w-xl max-h-[92vh] overflow-auto rounded-[28px] p-5 shadow-2xl fade">
  <div class="flex justify-between items-start">
   <div><h3 class="text-xl font-black">Корзина</h3><p class="text-xs text-slate-500 mt-1">Проверьте заказ перед оплатой</p></div>
   <button onclick="closeModal('cartModal')" class="w-9 h-9 rounded-xl bg-slate-100 text-slate-500 text-xl">×</button>
  </div>
  <div id="cartItems" class="mt-5 space-y-2"></div>
  <div class="mt-5 grid sm:grid-cols-2 gap-3">
    <div>
      <label class="text-xs font-bold text-slate-600">Время выдачи</label>
      <select id="pickup" class="mt-1 w-full rounded-xl border border-slate-200 bg-slate-50 p-3 text-sm"></select>
    </div>
    <div class="bg-slate-50 rounded-xl p-3">
      <div class="flex justify-between text-xs text-slate-500"><span>Без скидки</span><b id="before">0 ₽</b></div>
      <div class="flex justify-between text-xs text-emerald-700 mt-1"><span>Кампус −5%</span><b id="discount">−0 ₽</b></div>
      <div class="flex justify-between font-black mt-2 pt-2 border-t"><span>Итого</span><span id="total" class="text-rose-700">0 ₽</span></div>
    </div>
  </div>
  <div id="allergens" class="hidden mt-3 p-3 rounded-xl bg-amber-50 border border-amber-200 text-amber-800 text-xs"></div>
  <button onclick="checkout()" id="checkout" class="mt-4 w-full rounded-2xl bg-rose-700 hover:bg-rose-800 text-white py-4 font-black shadow-lg">Оплатить и оформить заказ</button>
 </div>
</div>

<div id="dishModal" class="hidden fixed inset-0 z-50 modal-bg p-3 sm:p-6 items-end sm:items-center justify-center">
 <div class="mobile-sheet bg-white w-full max-w-2xl max-h-[92vh] overflow-auto rounded-[28px] shadow-2xl fade">
  <div id="dishContent"></div>
 </div>
</div>

<div id="qrModal" class="hidden fixed inset-0 z-[60] bg-rose-800 p-5 text-white items-center justify-center">
 <div class="w-full max-w-md text-center">
  <div class="text-5xl">🎫</div>
  <h3 class="text-3xl font-black mt-3">Ваш заказ</h3>
  <p id="qrId" class="text-rose-100 mt-1"></p>
  <div class="bg-white p-4 rounded-3xl mt-5 inline-block shadow-2xl"><img id="qr" class="w-56 h-56"></div>
  <div id="qrStatus" class="mt-5 px-4 py-3 rounded-2xl bg-black/20 font-bold"></div>
  <div id="timeline" class="mt-4 text-left space-y-2"></div>
  <div class="flex gap-2 mt-5">
    <button onclick="closeModal('qrModal')" class="flex-1 rounded-2xl bg-white text-rose-700 py-3.5 font-black">Закрыть</button>
    <button id="pickupBtn" onclick="pickup()" class="hidden flex-1 rounded-2xl bg-emerald-400 text-slate-950 py-3.5 font-black">Забрать</button>
  </div>
 </div>
</div>

<div id="ordersModal" class="hidden fixed inset-0 z-50 modal-bg p-3 sm:p-6 items-end sm:items-center justify-center">
 <div class="mobile-sheet bg-white w-full max-w-2xl max-h-[92vh] overflow-auto rounded-[28px] p-5 shadow-2xl fade">
  <div class="flex justify-between">
   <div><h3 class="text-xl font-black">История заказов</h3><p class="text-xs text-slate-500 mt-1">Последние заказы студента</p></div>
   <button onclick="closeModal('ordersModal')" class="w-9 h-9 rounded-xl bg-slate-100 text-slate-500 text-xl">×</button>
  </div>
  <div id="ordersList" class="mt-5 space-y-3"></div>
 </div>
</div>

<div id="authModal" class="hidden fixed inset-0 z-[70] modal-bg p-3 sm:p-6 items-end sm:items-center justify-center">
 <div class="mobile-sheet bg-white w-full max-w-md rounded-[28px] p-5 shadow-2xl fade">
  <div class="flex items-center justify-between"><div><div class="text-[10px] uppercase tracking-[.18em] text-rose-600 font-black">NETI ID</div><h3 id="authTitle" class="text-2xl font-black mt-1">Вход</h3></div><button onclick="closeModal('authModal')" class="w-10 h-10 rounded-xl bg-slate-100 text-xl">×</button></div>
  <p id="authSubtitle" class="text-sm text-slate-500 mt-2">Войдите, чтобы оформлять заказы и сохранять избранное.</p>
  <div id="authNameWrap" class="hidden mt-5"><label class="text-xs font-bold">Имя</label><input id="authName" class="mt-1 w-full rounded-2xl border p-3.5" placeholder="Иван Иванов"></div>
  <div class="mt-4"><label class="text-xs font-bold">Email</label><input id="authEmail" type="email" autocomplete="email" class="mt-1 w-full rounded-2xl border p-3.5" placeholder="student@nstu.ru"></div>
  <div class="mt-4"><label class="text-xs font-bold">Пароль</label><input id="authPassword" type="password" autocomplete="current-password" class="mt-1 w-full rounded-2xl border p-3.5" placeholder="Минимум 8 символов"></div>
  <button id="authSubmit" onclick="submitAuth()" class="mt-5 w-full rounded-2xl bg-rose-700 text-white py-4 font-black">Войти</button>
  <button id="authSwitch" onclick="switchAuthMode()" class="mt-3 w-full text-sm font-bold text-slate-600">Нет аккаунта? Создать</button>
 </div>
</div>

<div id="accountModal" class="hidden fixed inset-0 z-[65] modal-bg p-3 sm:p-6 items-end sm:items-center justify-center">
 <div class="mobile-sheet bg-white w-full max-w-md rounded-[28px] p-5 shadow-2xl fade">
  <div class="flex justify-between"><div><div class="text-[10px] uppercase tracking-[.18em] text-emerald-600 font-black">NETI ID</div><h3 class="text-2xl font-black">Мой аккаунт</h3></div><button onclick="closeModal('accountModal')" class="w-10 h-10 rounded-xl bg-slate-100 text-xl">×</button></div>
  <div class="mt-5 rounded-3xl bg-slate-950 text-white p-5"><div id="accountName" class="text-xl font-black">Студент</div><div id="accountEmail" class="text-sm text-slate-400 mt-1">—</div><div class="grid grid-cols-2 gap-3 mt-5"><div class="rounded-2xl bg-white/10 p-3"><div class="text-xs text-slate-400">Бонусы</div><b id="accountPoints">0</b></div><div class="rounded-2xl bg-white/10 p-3"><div class="text-xs text-slate-400">Уровень</div><b id="accountLevel">NEW</b></div></div></div>
  <button onclick="logout()" class="mt-4 w-full rounded-2xl bg-slate-100 py-4 font-black text-slate-700">Выйти из аккаунта</button>
 </div>
</div>

<script>
let USER_ID = null;
let AUTH_MODE = "login";
const DISCOUNT = 0.05;
const CATEGORY_NAMES = {
  all:'Всё', combo:'🍱 Комбо', hot:'🥘 Горячее', soup:'🥣 Супы',
  salad:'🥗 Салаты', pastry:'🥐 Выпечка', drink:'🥤 Напитки'
};

let menu = [];
function readStorageJSON(key, fallback){
  try{
    const raw=localStorage.getItem(key);
    if(!raw)return fallback;
    const value=JSON.parse(raw);
    return value ?? fallback;
  }catch{
    localStorage.removeItem(key);
    return fallback;
  }
}
let cart = readStorageJSON('neti_food_cart', {});
let favorites = readStorageJSON('neti_food_favorites', []);
if(!cart || typeof cart!=='object' || Array.isArray(cart)) cart={};
if(!Array.isArray(favorites)) favorites=[];
favorites=favorites.map(Number).filter(Number.isFinite);
let category = 'all';
let filters = {vegan:false,lactose:false,available:false};
let activeRequests = {menu:0,lockers:0,sync:0};
let checkoutInProgress = false;
let activeOrder = null;
let authReady = false;
let searchTimer = null;

const $ = id => document.getElementById(id);
const money = n => {
  const value=Number(n);
  return `${Number.isFinite(value)?value.toFixed(2).replace('.00',''):'0'} ₽`;
};
const escapeHTML = value => String(value??'').replace(/[&<>"']/g,ch=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[ch]));
const safeImage = value => {
  const url=String(value||'');
  return /^https:\/\/(images\.unsplash\.com|loremflickr\.com)\//i.test(url) ? url : 'https://loremflickr.com/700/500/food?lock=9999';
};
const friendlyError = error => {
  const message=String(error?.message||'');
  if(!navigator.onLine) return 'Нет соединения с интернетом. Проверьте сеть и повторите попытку.';
  if(/Failed to fetch|NetworkError|Load failed/i.test(message)) return 'Не удалось связаться с сервером. Повторите попытку через несколько секунд.';
  return message || 'Произошла ошибка. Повторите попытку.';
};

function toast(text, type='info'){
  const el=document.createElement('div');
  el.className=`rounded-2xl px-4 py-3 text-sm font-bold shadow-2xl fade ${type==='error'?'bg-rose-700':type==='success'?'bg-emerald-600':'bg-slate-900'} text-white`;
  el.textContent=text;
  $('toast').appendChild(el);
  setTimeout(()=>el.remove(),3000);
}
function saveCart(){
  try{localStorage.setItem('neti_food_cart',JSON.stringify(cart));}
  catch{toast('Не удалось сохранить корзину на этом устройстве','error');}
}
function saveFav(){
  try{localStorage.setItem('neti_food_favorites',JSON.stringify(favorites));}
  catch{toast('Не удалось сохранить избранное','error');}
}

function activeOrderKey(){
  return USER_ID ? `neti_food_active_order_${USER_ID}` : null;
}
function saveActiveOrder(order){
  activeOrder=order||null;
  const key=activeOrderKey();
  if(!key)return;
  try{
    if(order && order.status!=='COMPLETED') localStorage.setItem(key,JSON.stringify(order));
    else localStorage.removeItem(key);
  }catch{
  }
}
function clearActiveOrder(){
  activeOrder=null;
  localStorage.removeItem('neti_food_active_order');
  const key=activeOrderKey();
  if(key) localStorage.removeItem(key);
}
function restoreActiveOrderCache(){
  localStorage.removeItem('neti_food_active_order');
  if(!USER_ID){ clearActiveOrder(); return; }
  try{
    const raw=localStorage.getItem(activeOrderKey());
    activeOrder=raw?JSON.parse(raw):null;
  }catch{ activeOrder=null; }
}
function closeModal(id){$(id).classList.add('hidden');$(id).classList.remove('flex')}
function openModal(id){$(id).classList.remove('hidden');$(id).classList.add('flex')}

async function api(url, options={}){
  const controller=new AbortController();
  const timeout=setTimeout(()=>controller.abort(),15000);
  try{
    const request={...options,credentials:'same-origin',signal:options.signal||controller.signal};
    const res=await fetch(url,request);
    let data={};
    const contentType=res.headers.get('content-type')||'';
    if(contentType.includes('application/json')){
      try{data=await res.json()}catch{}
    }
    if(!res.ok){
      const detail=Array.isArray(data.detail)
        ? data.detail.map(x=>x?.msg||x?.message).filter(Boolean).join('; ')
        : data.detail;
      throw new Error(detail||`Ошибка сервера (${res.status})`);
    }
    return data;
  }catch(e){
    if(e?.name==='AbortError') throw new Error('Сервер отвечает слишком долго. Повторите попытку.');
    throw e;
  }finally{
    clearTimeout(timeout);
  }
}

function renderCategories(){
  $('categories').innerHTML=Object.entries(CATEGORY_NAMES).map(([k,v])=>`
    <button onclick="setCategory('${k}')" class="shrink-0 rounded-xl px-4 py-2 text-xs font-bold border ${category===k?'bg-rose-700 text-white border-rose-700 shadow':'bg-white text-slate-600 border-slate-200'}">${v}</button>
  `).join('');
}

function renderFilters(){
  $('vegan').className=`filter rounded-xl px-3 py-2 text-xs font-semibold border ${filters.vegan?'bg-emerald-100 text-emerald-800 border-emerald-300':'bg-white border-slate-200'}`;
  $('lactose').className=`filter rounded-xl px-3 py-2 text-xs font-semibold border ${filters.lactose?'bg-blue-100 text-blue-800 border-blue-300':'bg-white border-slate-200'}`;
  $('available').className=`filter rounded-xl px-3 py-2 text-xs font-semibold border ${filters.available?'bg-violet-100 text-violet-800 border-violet-300':'bg-white border-slate-200'}`;
}

function openAuth(mode="login"){
  AUTH_MODE=mode;
  $('authTitle').textContent=mode==='login'?'Вход':'Создать аккаунт';
  $('authSubtitle').textContent=mode==='login'?'Войдите, чтобы оформлять заказы и сохранять избранное.':'Создайте NETI ID за минуту.';
  $('authNameWrap').classList.toggle('hidden', mode==='login');
  $('authPassword').autocomplete=mode==='login'?'current-password':'new-password';
  $('authSubmit').textContent=mode==='login'?'Войти':'Создать аккаунт';
  $('authSwitch').textContent=mode==='login'?'Нет аккаунта? Создать':'Уже есть аккаунт? Войти';
  openModal('authModal');
}
function switchAuthMode(){openAuth(AUTH_MODE==='login'?'register':'login')}
async function submitAuth(){
  try{
    const email=$('authEmail').value.trim().toLowerCase();
    const password=$('authPassword').value;
    const body=AUTH_MODE==='login'
      ? {email,password}
      : {name:$('authName').value.trim(),email,password};
    const data=await api('/api/auth/'+AUTH_MODE,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
    USER_ID=data.user_id; closeModal('authModal'); updateAccountUI(data); authReady=true; await syncActive(); toast(AUTH_MODE==='login'?'С возвращением 👋':'Аккаунт создан 🎉','success'); loadMenu();
  }catch(e){toast(friendlyError(e),'error')}
}
function updateAccountUI(data){
  USER_ID=Number(data.user_id);
  restoreActiveOrderCache();
  $('accountBtn').textContent=(data.name||'Аккаунт').slice(0,12);
  $('accountName').textContent=data.name||'Студент'; $('accountEmail').textContent=data.email||'—';
  $('accountPoints').textContent=data.points??0; $('accountLevel').textContent=data.level||'NEW';
}
async function initAuth(){
  USER_ID=null;
  activeOrder=null;
  authReady=false;
  updateActive();
  try{
    const me=await api('/api/auth/me');
    updateAccountUI(me);
    authReady=true;
    return true;
  }catch(e){
    USER_ID=null;
    activeOrder=null;
    localStorage.removeItem('neti_food_active_order');
    $('accountBtn').textContent='NETI ID';
    authReady=true;
    updateActive();
    return false;
  }
}
async function openAccount(){
  if(!USER_ID){openAuth('login');return}
  try{const me=await api('/api/auth/me'); updateAccountUI(me); openModal('accountModal')}catch(e){USER_ID=null;openAuth('login')}
}
async function logout(){try{await api('/api/auth/logout',{method:'POST'});clearActiveOrder();USER_ID=null;authReady=true;closeModal('accountModal');updateActive();toast('Вы вышли из аккаунта');}catch(e){toast(friendlyError(e),'error')}}

async function loadMenu(){
  const requestId=++activeRequests.menu;
  const q=$('search').value.trim();
  $('menu').innerHTML=Array.from({length:6},()=>`<div class="h-72 rounded-3xl skeleton"></div>`).join('');
  try{
    const params=new URLSearchParams({category,search:q});
    if(filters.vegan)params.set('is_vegan','true');
    if(filters.lactose)params.set('is_lactose_free','true');
    if(filters.available)params.set('only_available','true');
    const result=await api('/api/menu?'+params.toString());
    if(requestId!==activeRequests.menu)return;
    menu=Array.isArray(result)?result:[];
    render();
  }catch(e){
    if(requestId!==activeRequests.menu)return;
    $('menu').innerHTML=`<div class="sm:col-span-2 lg:col-span-3 p-10 text-center text-rose-600">
      <div class="text-3xl mb-2">⚠️</div><b>Не удалось загрузить меню</b>
      <div class="text-sm text-slate-500 mt-2">${escapeHTML(friendlyError(e))}</div>
      <button onclick="loadMenu()" class="mt-4 rounded-xl bg-rose-700 text-white px-4 py-2 font-bold">Повторить</button>
    </div>`;
  }
}

function render(){
  renderCategories();renderFilters();
  const sort=$('sort').value;
  let list=[...menu];
  if(sort==='price-asc')list.sort((a,b)=>a.price_rub-b.price_rub);
  if(sort==='price-desc')list.sort((a,b)=>b.price_rub-a.price_rub);
  if(sort==='calories')list.sort((a,b)=>a.kbju.calories-b.kbju.calories);
  if(sort==='stock')list.sort((a,b)=>b.stock-a.stock);
  $('menu-subtitle').textContent=`Найдено блюд: ${list.length} • В наличии: ${list.filter(x=>x.stock>0).length}`;
  if(!list.length){
    $('menu').innerHTML=`<div class="sm:col-span-2 lg:col-span-3 bg-white border rounded-3xl p-12 text-center"><div class="text-5xl">🍽️</div><div class="font-black mt-3">Ничего не найдено</div><div class="text-sm text-slate-500 mt-1">Попробуйте изменить фильтры или запрос</div></div>`;
    updateCart();
    return;
  }
  $('menu').innerHTML=list.map(dishCard).join('');
  updateCart();
}

function dishCard(d){
  const qty=cart[d.id]||0, fav=favorites.includes(d.id), out=d.stock<=0;
  return `<article id="dish-${d.id}" class="card bg-white border border-slate-200 rounded-3xl overflow-hidden ${out?'opacity-60':''}">
    <div class="relative h-44 bg-slate-100 cursor-pointer" onclick="openDish(${d.id})">
      <img src="${safeImage(d.image_url)}" loading="lazy" decoding="async" class="dish-photo w-full h-full object-cover" onerror="this.onerror=null;this.src='https://loremflickr.com/700/500/food?lock=9999'">
      <div class="absolute inset-x-0 top-0 p-3 flex justify-between">
        <span class="text-[10px] font-black px-2.5 py-1 rounded-full bg-white/90 backdrop-blur">${d.is_hot?'🔥 Горячее':'❄️ Холодное'}</span>
        <button onclick="event.stopPropagation();toggleFav(${d.id})" class="w-8 h-8 rounded-xl bg-white/90 text-lg">${fav?'❤️':'♡'}</button>
      </div>
      ${out?'<div class="absolute inset-0 bg-slate-950/30 flex items-center justify-center"><span class="bg-white text-slate-800 px-3 py-2 rounded-xl font-black text-xs">Нет в наличии</span></div>':''}
    </div>
    <div class="p-4">
      <div class="flex gap-2 justify-between items-start">
        <h3 class="font-black text-sm leading-snug cursor-pointer" onclick="openDish(${d.id})">${escapeHTML(d.name)}</h3>
        <b class="text-rose-700 whitespace-nowrap">${money(d.price_rub)}</b>
      </div>
      <p class="text-xs text-slate-500 mt-1.5 line-clamp-2 min-h-8">${escapeHTML(d.description)}</p>
      <div class="flex flex-wrap gap-1 mt-3">
        ${d.is_vegan?'<span class="text-[9px] bg-emerald-50 text-emerald-700 px-2 py-1 rounded-lg font-bold">🌱 Vegan</span>':''}
        ${d.is_lactose_free?'<span class="text-[9px] bg-blue-50 text-blue-700 px-2 py-1 rounded-lg font-bold">🥛 Без лактозы</span>':''}
        <span class="text-[9px] bg-slate-100 text-slate-500 px-2 py-1 rounded-lg font-bold">${escapeHTML(d.weight_g)}</span>
      </div>
      <div class="mt-3 flex items-center justify-between gap-2">
        <div class="text-[10px] text-slate-400">${d.kbju.calories} ккал • Б ${d.kbju.proteins} • Ж ${d.kbju.fats} • У ${d.kbju.carbs}</div>
        ${out?`<span class="text-xs font-bold text-rose-500">Раскуплено</span>`:
        qty?`<div class="flex items-center gap-2"><button onclick="changeCart(${d.id},-1)" class="w-8 h-8 rounded-xl bg-slate-100 font-black">−</button><b>${qty}</b><button onclick="changeCart(${d.id},1)" class="w-8 h-8 rounded-xl bg-rose-700 text-white font-black">+</button></div>`:
        `<button onclick="changeCart(${d.id},1)" class="rounded-xl bg-rose-700 text-white px-3 py-2 text-xs font-black">В корзину +</button>`}
      </div>
    </div>
  </article>`;
}

function toggleFav(id){
  favorites=favorites.includes(id)?favorites.filter(x=>x!==id):[...favorites,id];
  saveFav();render();
}
function openDish(id){
  const d=menu.find(x=>x.id===id);if(!d)return;
  $('dishContent').innerHTML=`<div class="relative">
    <img src="${d.image_url}" class="w-full h-56 sm:h-72 object-cover">
    <button onclick="closeModal('dishModal')" class="absolute top-3 right-3 w-10 h-10 rounded-2xl bg-black/50 text-white text-xl">×</button>
  </div>
  <div class="p-5">
    <div class="flex justify-between gap-3"><h3 class="text-2xl font-black">${escapeHTML(d.name)}</h3><b class="text-xl text-rose-700">${money(d.price_rub)}</b></div>
    <p class="text-sm text-slate-500 mt-2 leading-relaxed">${escapeHTML(d.description)}</p>
    <div class="grid grid-cols-4 gap-2 mt-5">${[
      ['Ккал',d.kbju.calories],['Белки',d.kbju.proteins+' г'],['Жиры',d.kbju.fats+' г'],['Углеводы',d.kbju.carbs+' г']
    ].map(x=>`<div class="rounded-2xl bg-slate-50 p-3 text-center"><div class="font-black">${x[1]}</div><div class="text-[10px] text-slate-400">${x[0]}</div></div>`).join('')}</div>
    <div class="mt-4 flex flex-wrap gap-2">
      <span class="px-3 py-2 rounded-xl bg-slate-100 text-xs font-bold">Выход: ${escapeHTML(d.weight_g)}</span>
      ${d.is_vegan?'<span class="px-3 py-2 rounded-xl bg-emerald-50 text-emerald-700 text-xs font-bold">🌱 Веганское</span>':''}
      ${d.is_lactose_free?'<span class="px-3 py-2 rounded-xl bg-blue-50 text-blue-700 text-xs font-bold">🥛 Без лактозы</span>':''}
    </div>
    ${d.allergens.length?`<div class="mt-4 p-3 rounded-2xl bg-amber-50 text-amber-800 text-xs"><b>Аллергены:</b> ${d.allergens.map(escapeHTML).join(', ')}</div>`:''}
    <button onclick="changeCart(${d.id},1);closeModal('dishModal')" ${d.stock<=0?'disabled':''} class="mt-5 w-full rounded-2xl py-4 font-black ${d.stock>0?'bg-rose-700 text-white':'bg-slate-200 text-slate-400'}">${d.stock>0?'Добавить в корзину':'Нет в наличии'}</button>
  </div>`;
  openModal('dishModal');
}

function changeCart(id,delta){
  const d=menu.find(x=>x.id===id);if(!d)return;
  const next=(cart[id]||0)+delta;
  if(next<0)return;
  if(next>d.stock){toast(`Доступно только ${d.stock} шт.`,'error');return}
  if(next===0)delete cart[id];else cart[id]=next;
  saveCart();render();
  if(delta>0)toast('Добавлено в корзину','success');
}

function cartDetails(){
  return Object.entries(cart).map(([id,q])=>{
    const d=menu.find(x=>x.id===Number(id));return d?{d,q}:null;
  }).filter(Boolean);
}

function updateCart(){
  const items=cartDetails();
  const count=items.reduce((s,x)=>s+x.q,0);
  $('badge').textContent=count;
  if(!$('cartModal').classList.contains('hidden'))renderCartModal();
  updateActive();
}

function renderCartModal(){
  const items=cartDetails();
  if(!items.length){
    $('cartItems').innerHTML='<div class="py-10 text-center text-slate-400">Корзина пуста</div>';
  }else{
    $('cartItems').innerHTML=items.map(({d,q})=>`<div class="flex items-center gap-3 p-3 rounded-2xl bg-slate-50 border border-slate-100">
      <img src="${d.image_url}" class="w-14 h-14 rounded-xl object-cover">
      <div class="min-w-0 flex-1"><div class="font-bold text-sm truncate">${d.name}</div><div class="text-xs text-slate-400">${money(d.price_rub)} × ${q}</div></div>
      <div class="flex items-center gap-2"><button onclick="changeCart(${d.id},-1)" class="w-8 h-8 rounded-lg bg-white border">−</button><b>${q}</b><button onclick="changeCart(${d.id},1)" class="w-8 h-8 rounded-lg bg-rose-700 text-white">+</button></div>
    </div>`).join('');
  }
  const total=items.reduce((s,x)=>s+x.d.price_rub*x.q,0);
  const discount=total*DISCOUNT;
  $('before').textContent=money(total);
  $('discount').textContent='−'+money(discount);
  $('total').textContent=money(total-discount);
  const allergens=[...new Set(items.flatMap(x=>x.d.allergens))];
  if(allergens.length){$('allergens').classList.remove('hidden');$('allergens').innerHTML=`⚠️ <b>Аллергены в заказе:</b> ${allergens.map(escapeHTML).join(', ')}`;}
  else $('allergens').classList.add('hidden');
  $('checkout').disabled=!items.length;
  $('checkout').classList.toggle('opacity-50',!items.length);
}

async function openCart(){
  if(!cartDetails().length){toast('Корзина пуста');return}
  try{
    if(!$('pickup').options.length){
      const cfg=await api('/api/config');
      const slots=Array.isArray(cfg.pickup_slots)?cfg.pickup_slots:[];
      if(!slots.length) throw new Error('Временные слоты выдачи недоступны.');
      $('pickup').innerHTML=slots.map((x,i)=>`<option value="${escapeHTML(x)}" ${i===1?'selected':''}>${escapeHTML(x)}</option>`).join('');
    }
    renderCartModal();openModal('cartModal');
  }catch(e){toast(friendlyError(e),'error')}
}
function clearSearch(){$('search').value='';$('clear').classList.add('hidden');loadMenu()}
function debouncedLoad(){
  $('clear').classList.toggle('hidden',!$('search').value);
  clearTimeout(searchTimer);searchTimer=setTimeout(loadMenu,280);
}
function setCategory(c){category=c;loadMenu()}
function toggleFilter(k){filters[k]=!filters[k];loadMenu()}
function resetFilters(){category='all';filters={vegan:false,lactose:false,available:false};$('search').value='';loadMenu()}

async function checkout(){
  if(!USER_ID){openAuth("login");return;}
  if(checkoutInProgress)return;
  const items=cartDetails();
  if(!items.length)return;
  checkoutInProgress=true;
  $('checkout').disabled=true;$('checkout').textContent='Оформление...';
  const idemKey=`web-${USER_ID}-${Date.now()}-${crypto?.randomUUID?.()||Math.random().toString(36).slice(2)}`;
  try{
    const order=await api('/api/orders/create',{
      method:'POST',
      headers:{'Content-Type':'application/json','Idempotency-Key':idemKey},
      body:JSON.stringify({user_id:USER_ID,pickup_time:$('pickup').value,items:items.map(x=>({item_id:x.d.id,quantity:x.q}))})
    });
    cart={};saveCart();saveActiveOrder(order);
    closeModal('cartModal');await showOrder(order);loadMenu();toast(`Заказ #${order.order_id} создан`,'success');
  }catch(e){toast(friendlyError(e),'error')}
  finally{checkoutInProgress=false;$('checkout').disabled=false;$('checkout').textContent='Оплатить и оформить заказ'}
}

function statusText(s){
  return {PAID:'Оплачен • ждёт кухню',COOKING:'Готовится на кухне',READY:'Готов • ждёт вас',COMPLETED:'Получен'}[s]||s;
}

async function showOrder(order, persist=true){
  if(!USER_ID){openAuth('login');return;}
  if(persist)saveActiveOrder(order);
  $('qr').src='data:image/png;base64,'+order.qr_code;
  $('qrId').textContent=`#${order.order_id} • Выдача ${order.pickup_time}`;
  $('qrStatus').textContent=order.cell_number?`${statusText(order.status)} • Ячейка №${order.cell_number}`:statusText(order.status);
  $('pickupBtn').classList.toggle('hidden',order.status!=='READY');
  openModal('qrModal');
  await renderTimeline(order.order_id);
  updateActive();
}

async function renderTimeline(id){
  try{
    const events=await api(`/api/orders/${id}/events`);
    $('timeline').innerHTML=events.map(e=>`<div class="rounded-xl bg-white/10 p-3"><div class="flex gap-2 items-center"><span class="${e.done?'text-emerald-300':'text-white/40'}">●</span><b class="text-xs">${e.title}</b></div><div class="text-[10px] text-rose-100/70 ml-5 mt-1">${e.description} • ${e.created_at.replace('T',' ')}</div></div>`).join('');
  }catch{}
}

function updateActive(){
  const box=$('active');
  if(!authReady || !USER_ID || !activeOrder || activeOrder.status==='COMPLETED'){box.classList.add('hidden');return}
  box.classList.remove('hidden');
  box.innerHTML=`<div onclick="showOrder(activeOrder)" class="cursor-pointer rounded-3xl p-4 sm:p-5 text-white shadow-xl" style="background:linear-gradient(135deg,#0f172a,#881337)">
    <div class="flex justify-between gap-3"><div><div class="text-[10px] text-rose-200 font-black uppercase tracking-widest">Активный заказ</div><div class="text-lg font-black mt-1">#${activeOrder.order_id}</div></div><div class="text-right"><div class="text-xs font-bold text-emerald-300">${statusText(activeOrder.status)}</div><div class="text-[10px] text-slate-400 mt-1">${activeOrder.pickup_time}</div></div></div>
    <div class="mt-3 h-2 rounded-full bg-white/10 overflow-hidden"><div class="h-full rounded-full bg-emerald-400" style="width:${({PAID:25,COOKING:55,READY:85,COMPLETED:100})[activeOrder.status]||25}%"></div></div>
  </div>`;
}

async function pickup(){
  if(!USER_ID){openAuth('login');return;}
  if(!activeOrder)return;
  try{
    const order=await api(`/api/orders/${activeOrder.order_id}/pickup`,{method:'POST'});
    clearActiveOrder();
    closeModal('qrModal');updateActive();toast('Заказ получен. Приятного аппетита!','success');loadLockers();
  }catch(e){toast(friendlyError(e),'error')}
}

async function syncActive(){
  if(!authReady)return;
  if(!USER_ID){clearActiveOrder();updateActive();return;}
  if(activeRequests.sync)return;
  activeRequests.sync=1;
  try{
    const order=await api('/api/orders/active');
    if(!order){clearActiveOrder();updateActive();return;}
    const changed=!activeOrder || activeOrder.order_id!==order.order_id ||
      activeOrder.status!==order.status || activeOrder.cell_number!==order.cell_number;
    saveActiveOrder(order);
    updateActive();
    if(changed && !$('qrModal').classList.contains('hidden')){
      await showOrder(order,false);
    }
  }catch(e){
    if(/Сессия|вход|401|403/i.test(String(e.message||''))){
      clearActiveOrder();USER_ID=null;updateActive();
    }
  }finally{activeRequests.sync=0;}
}

async function openOrders(){
  openModal('ordersModal');
  try{
    const orders=await api(`/api/orders?user_id=${USER_ID}&limit=50`);
    $('ordersList').innerHTML=orders.length?orders.map(o=>`<button onclick='showOrder(${JSON.stringify(o).replace(/'/g,"&#39;")})' class="w-full text-left p-4 rounded-2xl border border-slate-200 hover:bg-slate-50">
      <div class="flex justify-between gap-2"><b>#${o.order_id}</b><span class="text-xs font-black ${o.status==='READY'?'text-emerald-600':'text-slate-500'}">${statusText(o.status)}</span></div>
      <div class="text-xs text-slate-500 mt-1 line-clamp-1">${o.items_summary}</div>
      <div class="flex justify-between mt-2 text-xs"><span>${o.pickup_time}</span><b>${money(o.total_price)}</b></div>
    </button>`).join(''):'<div class="py-10 text-center text-slate-400">Заказов пока нет</div>';
  }catch(e){$('ordersList').textContent=friendlyError(e)}
}

async function loadLockers(){
  if(activeRequests.lockers)return;
  activeRequests.lockers=1;
  try{
    const data=await api('/api/lockers');
    const cells=Array.isArray(data.cells)?data.cells:[];
    $('lockers').innerHTML=cells.map(c=>`<div class="rounded-2xl p-2 border ${c.occupied?(c.mode==='hot'?'border-rose-400 led-hot':'border-blue-400 led-cool'):'border-slate-800'} bg-slate-900 text-center">
      <div class="text-[9px] text-slate-500">№${escapeHTML(c.cell_number)}</div><div class="text-xs font-black ${c.mode==='hot'?'text-rose-300':'text-blue-300'}">${escapeHTML(c.temperature)}</div><div class="text-[9px] mt-1 ${c.occupied?'text-emerald-300':'text-slate-600'}">${c.occupied?'Заказ #'+escapeHTML(c.order_id):'Свободна'}</div>
    </div>`).join('');
  }catch(e){
    const box=$('lockers');
    if(box && !box.children.length) box.innerHTML='<div class="col-span-full text-center text-xs text-slate-500 py-5">Постаматы временно недоступны</div>';
  }finally{activeRequests.lockers=0}
}

let kitchenOpen=false;
async function toggleKitchen(){
  kitchenOpen=!kitchenOpen;$('kitchen').classList.toggle('hidden',!kitchenOpen);
  if(kitchenOpen)await loadKitchen();
}
async function loadKitchen(){
  try{
    const [orders,stats,lockers]=await Promise.all([api('/api/orders?limit=100'),api('/api/stats'),api('/api/lockers')]);
    $('kitchen').innerHTML=`<div class="grid grid-cols-2 sm:grid-cols-4 gap-2 mb-4">${[
      ['Сегодня',stats.today_orders],['Выручка',money(stats.today_revenue)],['В работе',stats.status_counts.COOKING||0],['Свободно',stats.free_lockers]
    ].map(x=>`<div class="bg-slate-50 rounded-2xl p-3"><div class="text-[10px] text-slate-400">${x[0]}</div><div class="font-black text-lg">${x[1]}</div></div>`).join('')}</div>
    <div class="space-y-2">${orders.filter(o=>o.status!=='COMPLETED').map(o=>`<div class="p-3 rounded-2xl border bg-white">
      <div class="flex justify-between gap-2"><b class="text-sm">#${o.order_id}</b><span class="text-[10px] font-black px-2 py-1 rounded-lg bg-slate-100">${statusText(o.status)}</span></div>
      <div class="text-xs text-slate-500 mt-1">${o.items_summary}</div>
      <div class="flex gap-2 mt-3">
       ${o.status==='PAID'?`<button onclick="kCooking(${o.order_id})" class="px-3 py-2 rounded-xl bg-amber-500 text-white text-[11px] font-black">В работу</button>`:''}
       ${o.status==='COOKING'?`<button onclick="kReady(${o.order_id})" class="px-3 py-2 rounded-xl bg-emerald-600 text-white text-[11px] font-black">В первую свободную ячейку</button>`:''}
      </div>
    </div>`).join('')||'<div class="text-center py-8 text-slate-400">Активных заказов нет</div>'}</div>`;
  }catch(e){$('kitchen').textContent=friendlyError(e)}
}
async function kCooking(id){try{await api(`/api/orders/${id}/status/cooking`,{method:'POST'});toast('Заказ передан в готовку','success');loadKitchen();loadLockers();syncActive()}catch(e){toast(friendlyError(e),'error')}}
async function kReady(id){try{const o=await api(`/api/orders/${id}/ready`,{method:'POST'});toast(`Заказ #${id} помещён в ячейку №${o.cell_number}`,'success');loadKitchen();loadLockers();syncActive()}catch(e){toast(friendlyError(e),'error')}}

async function redeemCoffee(){
  try{
    const r = await api(`/api/v6/cashback/${USER_ID}/redeem`,{method:'POST'});
    toast(`Код для бариста: ${r.redeem_code}`,'success');
    document.getElementById('v5Dash')?.remove();
    openV5Dashboard();
  }catch(e){toast(friendlyError(e),'error')}
}

async function openV5Dashboard(){
  if(!USER_ID){
    openAuth('login');
    return;
  }
  try{
    const [info, analytics, loyalty, favorites, notes, cashback] = await Promise.all([
      api('/api/v5/info'),
      api('/api/v5/analytics'),
      api(`/api/v5/users/${USER_ID}/loyalty`),
      api(`/api/v5/users/${USER_ID}/favorites`),
      api(`/api/v5/users/${USER_ID}/notifications?unread_only=true`),
      api(`/api/v6/cashback/${USER_ID}`)
    ]);
    const html = `
      <div class="fixed inset-0 z-[90] modal-bg p-3 sm:p-6 flex items-end sm:items-center justify-center" id="v5Dash">
       <div class="bg-white w-full max-w-4xl max-h-[92vh] overflow-auto rounded-[30px] p-5 shadow-2xl">
        <div class="flex justify-between gap-3">
          <div><div class="text-[10px] font-black tracking-[.2em] text-emerald-600">NETI_FOOD 7.0</div>
          <h2 class="text-2xl font-black">Центр кампуса</h2>
          <p class="text-xs text-slate-500 mt-1">${info.modules.length} модулей активны</p></div>
          <button onclick="document.getElementById('v5Dash').remove()" class="w-10 h-10 rounded-xl bg-slate-100 text-xl">×</button>
        </div>
        <div class="grid sm:grid-cols-4 gap-3 mt-5">
          ${[
            ['Заказы',analytics.orders_total],
            ['Выручка',money(analytics.revenue_total)],
            ['Баллы',loyalty.points],
            ['Уведомления',notes.items.length]
          ].map(x=>`<div class="rounded-2xl bg-slate-50 p-4"><div class="text-[10px] text-slate-400">${x[0]}</div><div class="text-xl font-black mt-1">${x[1]}</div></div>`).join('')}
        </div>
        <div class="grid lg:grid-cols-2 gap-4 mt-5">
          <div class="rounded-2xl border p-4">
            <b>🎓 Программа лояльности</b>
            <p class="text-sm text-slate-500 mt-2">Уровень: <b>${loyalty.level}</b></p>
            <div class="h-2 rounded-full bg-slate-100 mt-3 overflow-hidden"><div class="h-full bg-emerald-500" style="width:${Math.min(100,(loyalty.points%1000)/10)}%"></div></div>
            <p class="text-[10px] text-slate-400 mt-2">${loyalty.points} баллов</p>
          </div>
          <div class="rounded-2xl border p-4">
            <b>❤️ Избранное</b>
            <p class="text-sm text-slate-500 mt-2">${favorites.items.length} блюд сохранено</p>
            <p class="text-xs text-slate-400 mt-2">Избранное синхронизируется с сервером.</p>
          </div>
          <div class="rounded-2xl border p-4 lg:col-span-2 bg-gradient-to-br from-amber-50 to-white">
            <div class="flex justify-between items-center">
              <b>☕ Студенческий кэшбэк</b>
              ${cashback.free_coffees_available>0?`<button onclick="redeemCoffee()" class="px-3 py-1.5 rounded-xl bg-amber-500 text-white text-xs font-bold">Получить кофе (${cashback.free_coffees_available})</button>`:''}
            </div>
            <p class="text-sm text-slate-500 mt-2">Каждый ${cashback.target}-й полноценный обед — кофе в подарок.</p>
            <div class="h-2 rounded-full bg-slate-100 mt-3 overflow-hidden"><div class="h-full bg-amber-500" style="width:${Math.round((cashback.target-cashback.remaining_to_next_coffee)/cashback.target*100)}%"></div></div>
            <p class="text-[10px] text-slate-400 mt-2">Обедов оформлено: ${cashback.hot_lunches_count} • до следующего кофе: ${cashback.remaining_to_next_coffee}</p>
          </div>
          <div class="rounded-2xl border p-4 lg:col-span-2">
            <b>📊 Статусы заказов</b>
            <div class="flex flex-wrap gap-2 mt-3">${Object.entries(analytics.statuses).map(([k,v])=>`<span class="px-3 py-2 rounded-xl bg-slate-100 text-xs font-bold">${statusText(k)}: ${v}</span>`).join('')}</div>
          </div>
        </div>
       </div>
      </div>`;
    document.body.insertAdjacentHTML('beforeend',html);
  }catch(e){toast(friendlyError(e),'error')}
}

function scrollToMenu(){window.scrollTo({top:document.querySelector('#menu').offsetTop-90,behavior:'smooth'});}
async function showFavorites(){
  if(!favorites.length){toast('В избранном пока пусто');return;}
  category='all';filters={vegan:false,lactose:false,available:false};$('search').value='';await loadMenu();
  setTimeout(()=>{const first=menu.find(x=>favorites.includes(x.id));if(first)document.getElementById(`dish-${first.id}`)?.scrollIntoView({behavior:'smooth',block:'center'});},100);
}
function loadSmartPicks(){
  const available=menu.filter(d=>d.stock>0);
  if(!available.length){$('smartPicks').innerHTML='<div class="text-sm text-slate-400">Сейчас нет доступных блюд.</div>';return;}
  const favSet=new Set(favorites);
  const picks=[...available].sort((a,b)=>{const score=d=>(favSet.has(d.id)?100:0)+(d.is_hot?8:0)+Math.min(d.stock,20)*.3+(d.price_rub<=60?6:0)+(d.kbju.calories<=350?4:0);return score(b)-score(a);}).slice(0,6);
  $('smartPicks').innerHTML=picks.map(d=>`<button onclick="openDish(${d.id})" class="snap-item shrink-0 w-[220px] text-left rounded-2xl border border-slate-200 overflow-hidden bg-white shadow-sm"><img src="${d.image_url}" class="w-full h-28 object-cover" loading="lazy" onerror="this.style.display='none'"><div class="p-3"><div class="text-[10px] text-rose-600 font-black">${favSet.has(d.id)?'❤️ Избранное':'⚡ Быстрый выбор'}</div><div class="font-black text-sm mt-1 line-clamp-2">${d.name}</div><div class="flex items-center justify-between mt-2"><span class="text-xs text-slate-400">${d.kbju.calories} ккал</span><b class="text-rose-700">${money(d.price_rub)}</b></div></div></button>`).join('');
}
async function loadV5Quick(){
  const box=$('v5Quick');
  if(!USER_ID){
    if(box) box.innerHTML=[
      ['📦','—','заказов'],
      ['₽','—','оборот'],
      ['⭐','—','войдите в NETI ID'],
      ['🔔','—','уведомлений']
    ].map(x=>`<div class="rounded-2xl bg-white/10 border border-white/10 p-3"><div>${x[0]}</div><div class="font-black mt-1">${x[1]}</div><div class="text-[9px] text-slate-400">${x[2]}</div></div>`).join('');
    return;
  }
  const uid=Number(USER_ID);
  if(!Number.isInteger(uid)||uid<1) return;
  try{
    const [a,l,n]=await Promise.all([
      api('/api/v5/analytics'),
      api(`/api/v5/users/${uid}/loyalty`),
      api(`/api/v5/users/${uid}/notifications?unread_only=true`)
    ]);
    const box=$('v5Quick');
    if(box) box.innerHTML=[
      ['📦',a.orders_total,'заказов'],
      ['₽',money(a.revenue_total),'оборот'],
      ['⭐',l.points,'баллов'],
      ['🔔',n.items.length,'новых']
    ].map(x=>`<div class="rounded-2xl bg-white/10 border border-white/10 p-3"><div>${x[0]}</div><div class="font-black mt-1">${x[1]}</div><div class="text-[9px] text-slate-400">${x[2]}</div></div>`).join('');
  }catch{}
}

function openCommandPalette(){
  const p=$('commandPalette'); if(!p)return;
  p.classList.remove('hidden');p.classList.add('flex');
  $('commandInput').value='';renderCommandResults('');
  setTimeout(()=>$('commandInput').focus(),20);
}
function closeCommandPalette(){const p=$('commandPalette');if(p){p.classList.add('hidden');p.classList.remove('flex')}}
function renderCommandResults(q){
  const query=(q||'').trim().toLowerCase();
  const actions=[
    ['🍽️','Открыть меню',()=>scrollToMenu()],
    ['❤️','Избранное',()=>showFavorites()],
    ['🛒','Корзина',()=>openCart()],
    ['📦','Мои заказы',()=>openOrders()],
    ['👤','NETI ID',()=>openAccount()],
  ];
  const dishes=menu.filter(d=>!query||d.name.toLowerCase().includes(query)).slice(0,8)
    .map(d=>['🍴',d.name,()=>openDish(d.id)]);
  const rows=(query?dishes:actions).map((x,i)=>`<button data-cmd="${i}" class="w-full text-left p-3 rounded-2xl hover:bg-slate-50 flex items-center gap-3"><span class="w-9 h-9 rounded-xl bg-rose-50 flex items-center justify-center">${x[0]}</span><span class="font-bold text-sm">${x[1]}</span></button>`).join('');
  $('commandResults').innerHTML=rows||'<div class="p-6 text-center text-slate-400">Ничего не найдено</div>';
  [...$('commandResults').querySelectorAll('[data-cmd]')].forEach((b,i)=>{
    const source=query?dishes:actions;b.onclick=()=>{closeCommandPalette();source[i][2]()}
  });
}
document.addEventListener('keydown',e=>{
  if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='k'){e.preventDefault();openCommandPalette()}
  if(e.key==='Escape')closeCommandPalette();
});
document.addEventListener('click',e=>{
  if(e.target===$('commandPalette'))closeCommandPalette();
});
document.addEventListener('input',e=>{if(e.target.id==='commandInput')renderCommandResults(e.target.value)});

function hideSplash(status='Готово'){
  const s=$('appSplash'), label=$('splashStatus');
  if(label) label.textContent=status;
  setTimeout(()=>s?.classList.add('hide'),320);
}
function updateNetworkChip(){
  const chip=$('networkChip');
  if(!chip)return;
  const online=navigator.onLine;
  chip.innerHTML=`<i style="background:${online?'#34d399':'#fb7185'}"></i><b>${online?'ONLINE':'OFFLINE'}</b>`;
}
window.addEventListener('online',updateNetworkChip);
window.addEventListener('offline',updateNetworkChip);
updateNetworkChip();

function updateInstallButton(){
  const btn=$('installBtn');
  if(!btn)return;
  const standalone=window.matchMedia('(display-mode: standalone)').matches || window.navigator.standalone;
  const mobile=window.matchMedia('(max-width: 640px)').matches;
  if(standalone){document.body.classList.add('pwa-installed');btn.classList.add('hidden');return;}
  if(mobile) btn.classList.remove('hidden');
}
window.matchMedia('(max-width: 640px)').addEventListener?.('change',updateInstallButton);

let deferredInstallPrompt=null;
window.addEventListener('beforeinstallprompt',e=>{
  e.preventDefault();
  deferredInstallPrompt=e;
  const btn=$('installBtn');
  if(btn && !window.matchMedia('(display-mode: standalone)').matches) btn.classList.remove('hidden');
  window.dispatchEvent(new CustomEvent('neti:pwa-install-ready'));
});
window.addEventListener('appinstalled',()=>{
  deferredInstallPrompt=null;
  document.body.classList.add('pwa-installed');
  $('installBtn')?.classList.add('hidden');
});
async function installNETIFood(){
  if(deferredInstallPrompt){
    deferredInstallPrompt.prompt();
    await deferredInstallPrompt.userChoice;
    deferredInstallPrompt=null;
    return true;
  }
  const ios=/iphone|ipad|ipod/i.test(navigator.userAgent);
  const standalone=window.matchMedia('(display-mode: standalone)').matches || window.navigator.standalone;
  if(ios && !standalone){ alert('На iPhone: нажмите «Поделиться» → «На экран Домой» → «Добавить».'); }
  else if(!standalone){ alert('Откройте меню браузера и выберите «Установить приложение» или «Добавить на главный экран».'); }
  return false;
}
window.installNETIFood=installNETIFood;
setTimeout(updateInstallButton,0);

async function registerServiceWorker(){
  if('serviceWorker' in navigator){
    try{await navigator.serviceWorker.register('/sw.js');}catch{}
  }
}
registerServiceWorker();

renderCategories();
renderFilters();

(async()=>{
  try{
    const authenticated=await initAuth();
    await loadMenu();
    await loadLockers();
    updateActive();
    if(authenticated){
      await Promise.allSettled([loadV5Quick(), loadSmartPicks()]);
    }else{
      await loadV5Quick();
    }
    hideSplash('Система готова • приятного аппетита');
  }catch(e){
    hideSplash('Открываем демо-режим');
    toast('Часть сервисов временно недоступна','info');
  }
})();

let refreshBusy=false;
setInterval(async()=>{
  if(refreshBusy)return;
  refreshBusy=true;
  try{
    await Promise.allSettled([
      syncActive(),
      loadLockers(),
      ...(kitchenOpen?[loadKitchen()]:[]),
      ...(USER_ID?[loadV5Quick()]:[])
    ]);
  }finally{refreshBusy=false;}
},7000);
</script>
</body>
</html>
"""

def hash_password(password: str, salt: bytes | None = None):
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 180_000)
    return f"pbkdf2_sha256$180000${base64.urlsafe_b64encode(salt).decode()}${base64.urlsafe_b64encode(digest).decode()}"

def verify_password(password: str, encoded: str) -> bool:
    try:
        scheme, rounds, salt_b64, digest_b64 = encoded.split("$")
        if scheme != "pbkdf2_sha256": return False
        salt = base64.urlsafe_b64decode(salt_b64.encode())
        expected = base64.urlsafe_b64decode(digest_b64.encode())
        actual = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, int(rounds))
        return secrets.compare_digest(actual, expected)
    except Exception:
        return False

def session_hash(token: str) -> str:
    return hashlib.sha256(token.encode()).hexdigest()

def auth_user(request: Request):
    token = request.cookies.get("neti_session")
    if not token: raise HTTPException(401, "Требуется вход в аккаунт")
    with db_lock, extra_db() as conn:
        row = conn.execute("""SELECT u.* FROM sessions s JOIN users u ON u.user_id=s.user_id
                              WHERE s.token_hash=? AND s.expires_at>?""", (session_hash(token), now_iso())).fetchone()
    if not row: raise HTTPException(401, "Сессия истекла. Войдите снова")
    return row

def require_same_user(request: Request, user_id: int):
    """Не позволяет клиенту подменить user_id в legacy/v5/v6 API."""
    user = auth_user(request)
    if int(user["user_id"]) != int(user_id):
        raise HTTPException(403, "Доступ запрещён")
    return user

def create_session(user_id: int) -> str:
    token = secrets.token_urlsafe(48)
    now = datetime.utcnow()
    created = now.isoformat(timespec="seconds") + "Z"
    expires = (now.replace(microsecond=0) + timedelta(days=30)).isoformat() + "Z"
    with db_lock, extra_db() as conn:
        conn.execute("INSERT INTO sessions(token_hash,user_id,created_at,expires_at) VALUES (?,?,?,?)",
                     (session_hash(token), user_id, created, expires))
    return token


@app.get("/api/v5/info")
def v5_info():
    return {
        "name": "NETI_Food",
        "version": "7.2.0",
        "build": "2026.09",
        "edition": "MEGA 7.2",
        "modules": [
            "orders", "smart-locker", "kitchen", "loyalty",
            "promo", "favorites", "reviews", "notifications",
            "analytics", "audit", "stock-control", "recommendations",
            "smart-search", "idempotent-orders", "security-controls", "v6-dashboard"
        ],
    }

@app.post("/api/auth/register")
def auth_register(payload: RegisterInput, response: Response, request: Request):
    rate_limit(request, "register", 5, 300)
    email = payload.email.strip().lower()
    if "@" not in email: raise HTTPException(400, "Введите корректный email")
    with db_lock, extra_db() as conn:
        if conn.execute("SELECT 1 FROM users WHERE email=?", (email,)).fetchone():
            raise HTTPException(409, "Аккаунт с таким email уже существует")
        row = conn.execute("SELECT COALESCE(MAX(user_id),100)+1 id FROM users").fetchone()
        user_id = int(row["id"])
        conn.execute("INSERT INTO users(user_id,name,email,password_hash,created_at) VALUES(?,?,?,?,?)",
                     (user_id, payload.name.strip(), email, hash_password(payload.password), now_iso()))
    token=create_session(user_id)
    response.set_cookie("neti_session", token, httponly=True, samesite="lax", secure=bool(os.getenv("NETI_FOOD_SECURE_COOKIE", "0") == "1"), max_age=60*60*24*30, path="/")
    audit(str(user_id), "REGISTER", email)
    return {"user_id": user_id, "name": payload.name.strip(), "email": email}

@app.post("/api/auth/login")
def auth_login(payload: LoginInput, response: Response, request: Request):
    rate_limit(request, "login", 10, 300)
    email=payload.email.strip().lower()
    with db_lock, extra_db() as conn:
        row=conn.execute("SELECT * FROM users WHERE email=?", (email,)).fetchone()
    if not row or not row["password_hash"] or not verify_password(payload.password, row["password_hash"]):
        raise HTTPException(401, "Неверный email или пароль")
    token=create_session(int(row["user_id"]))
    response.set_cookie("neti_session", token, httponly=True, samesite="lax", secure=bool(os.getenv("NETI_FOOD_SECURE_COOKIE", "0") == "1"), max_age=60*60*24*30, path="/")
    return {"user_id": row["user_id"], "name": row["name"], "email": row["email"]}

@app.post("/api/auth/logout")
def auth_logout(request: Request, response: Response):
    token=request.cookies.get("neti_session")
    if token:
        with db_lock, extra_db() as conn:
            conn.execute("DELETE FROM sessions WHERE token_hash=?", (session_hash(token),))
    response.delete_cookie("neti_session", path="/")
    return {"ok": True}

@app.get("/api/auth/me")
def auth_me(request: Request):
    row=auth_user(request)
    return {"user_id": row["user_id"], "name": row["name"], "email": row["email"], "points": row["points"], "level": row["level"]}

@app.post("/api/v5/users")
def create_or_update_user(payload: LoyaltyProfile, request: Request):
    require_same_user(request, payload.user_id)
    ensure_user(payload.user_id, payload.name)
    with db_lock, extra_db() as conn:
        conn.execute("UPDATE users SET name=? WHERE user_id=?", (payload.name, payload.user_id))
        row = conn.execute(
            "SELECT user_id,name,email,points,level,created_at FROM users WHERE user_id=?",
            (payload.user_id,)
        ).fetchone()
    return dict(row)

@app.get("/api/v5/users/{user_id}/loyalty")
def get_loyalty(user_id: int, request: Request):
    require_same_user(request, user_id)
    ensure_user(user_id)
    with db_lock, extra_db() as conn:
        row = conn.execute(
            "SELECT user_id,name,email,points,level,created_at FROM users WHERE user_id=?",
            (user_id,)
        ).fetchone()
    return dict(row) if row else {"user_id": user_id, "name": "Студент", "email": None, "points": 0, "level": "NEW"}

@app.post("/api/v5/promo/check")
def check_promo(payload: PromoApply, request: Request):
    require_same_user(request, payload.user_id)
    ensure_user(payload.user_id)
    code = payload.code.strip().upper()
    with db_lock, extra_db() as conn:
        row = conn.execute(
            "SELECT * FROM promo_codes WHERE code=? AND active=1", (code,)
        ).fetchone()
        if not row:
            raise HTTPException(404, "Промокод не найден или отключён")
        if row["used_count"] >= row["max_uses"]:
            raise HTTPException(400, "Лимит использования промокода исчерпан")
        used = conn.execute(
            "SELECT 1 FROM promo_users WHERE code=? AND user_id=?", (code, payload.user_id)
        ).fetchone()
        if used:
            raise HTTPException(400, "Этот промокод уже использован")
    return {"code": code, "discount_percent": row["discount_percent"], "valid": True}

@app.post("/api/v5/promo/use")
def use_promo(payload: PromoApply, request: Request):
    data = check_promo(payload, request)
    code = data["code"]
    with db_lock, extra_db() as conn:
        conn.execute(
            "INSERT INTO promo_users(code,user_id,used_at) VALUES (?,?,?)",
            (code, payload.user_id, now_iso())
        )
        updated = conn.execute(
            "UPDATE promo_codes SET used_count=used_count+1 "
            "WHERE code=? AND active=1 AND used_count < max_uses",
            (code,),
        )
        if updated.rowcount != 1:
            raise HTTPException(409, "Промокод больше недоступен")
    audit(str(payload.user_id), "PROMO_USED", code)
    return {"ok": True, **data}

@app.get("/api/v5/users/{user_id}/favorites")
def get_favorites(user_id: int, request: Request):
    require_same_user(request, user_id)
    with db_lock, extra_db() as conn:
        rows = conn.execute(
            "SELECT item_id FROM favorites WHERE user_id=? ORDER BY created_at DESC", (user_id,)
        ).fetchall()
    return {"items": [r["item_id"] for r in rows]}

@app.post("/api/v5/favorites/toggle")
def toggle_favorite(payload: FavoriteToggle, request: Request):
    require_same_user(request, payload.user_id)
    with db_lock, extra_db() as conn:
        row = conn.execute(
            "SELECT 1 FROM favorites WHERE user_id=? AND item_id=?",
            (payload.user_id, payload.item_id)
        ).fetchone()
        if row:
            conn.execute(
                "DELETE FROM favorites WHERE user_id=? AND item_id=?",
                (payload.user_id, payload.item_id)
            )
            active = False
        else:
            conn.execute(
                "INSERT INTO favorites(user_id,item_id,created_at) VALUES (?,?,?)",
                (payload.user_id, payload.item_id, now_iso())
            )
            active = True
    audit(str(payload.user_id), "FAVORITE_TOGGLE", f"{payload.item_id}:{active}")
    return {"item_id": payload.item_id, "favorite": active}

@app.post("/api/v5/reviews")
def create_review(payload: ReviewCreate, request: Request):
    require_same_user(request, payload.user_id)
    if not any(x.id == payload.item_id for x in MENU_DB):
        raise HTTPException(404, "Блюдо не найдено")
    with db_lock, extra_db() as conn:
        conn.execute(
            "INSERT INTO reviews(user_id,item_id,rating,text,created_at) VALUES (?,?,?,?,?)",
            (payload.user_id, payload.item_id, payload.rating, payload.text.strip(), now_iso())
        )
    audit(str(payload.user_id), "REVIEW_CREATED", f"item={payload.item_id};rating={payload.rating}")
    return {"ok": True}

@app.get("/api/v5/menu/{item_id}/reviews")
def item_reviews(item_id: int):
    with db_lock, extra_db() as conn:
        rows = conn.execute(
            "SELECT rating,text,created_at,user_id FROM reviews WHERE item_id=? ORDER BY id DESC LIMIT 50",
            (item_id,)
        ).fetchall()
    ratings = [int(r["rating"]) for r in rows]
    return {
        "item_id": item_id,
        "count": len(ratings),
        "average": round(statistics.mean(ratings), 2) if ratings else 0,
        "reviews": [dict(r) for r in rows],
    }

@app.get("/api/v5/users/{user_id}/notifications")
def notifications(user_id: int, request: Request, unread_only: bool = False):
    require_same_user(request, user_id)
    sql = "SELECT * FROM notifications WHERE user_id=?"
    args = [user_id]
    if unread_only:
        sql += " AND read=0"
    sql += " ORDER BY id DESC LIMIT 100"
    with db_lock, extra_db() as conn:
        rows = conn.execute(sql, args).fetchall()
    return {"items": [dict(r) for r in rows]}

@app.post("/api/v5/users/{user_id}/notifications/read")
def mark_notifications_read(user_id: int, request: Request):
    require_same_user(request, user_id)
    with db_lock, extra_db() as conn:
        conn.execute("UPDATE notifications SET read=1 WHERE user_id=?", (user_id,))
    return {"ok": True}

@app.get("/api/v5/analytics")
def analytics():
    with db_lock, db() as main, extra_db() as extra:
        total = main.execute("SELECT COUNT(*) c FROM orders").fetchone()["c"]
        revenue = main.execute("SELECT COALESCE(SUM(total_price),0) v FROM orders").fetchone()["v"]
        statuses = {
            r["status"]: r["c"]
            for r in main.execute("SELECT status,COUNT(*) c FROM orders GROUP BY status")
        }
        top_rows = main.execute(
            "SELECT items_summary FROM orders ORDER BY order_id DESC LIMIT 500"
        ).fetchall()
        review_count = extra.execute("SELECT COUNT(*) c FROM reviews").fetchone()["c"]
        favorites = extra.execute("SELECT COUNT(*) c FROM favorites").fetchone()["c"]
        users = extra.execute("SELECT COUNT(*) c FROM users").fetchone()["c"]
    return {
        "orders_total": total,
        "revenue_total": round(float(revenue), 2),
        "statuses": statuses,
        "users": users,
        "reviews": review_count,
        "favorites": favorites,
        "generated_at": now_iso(),
    }

@app.post("/api/v5/admin/stock")
def admin_stock(payload: AdminStockUpdate, token: str = Query("")):
    require_admin(token)
    get_menu_item(payload.item_id)
    with db_lock, db() as conn:
        conn.execute(
            "UPDATE menu_stock SET stock=? WHERE item_id=?",
            (payload.stock, payload.item_id)
        )
    audit("admin", "STOCK_UPDATE", f"item={payload.item_id};stock={payload.stock}")
    return {"ok": True, "item_id": payload.item_id, "stock": payload.stock}

@app.get("/api/v5/admin/audit")
def admin_audit(limit: int = Query(100, ge=1, le=500), token: str = Query("")):
    require_admin(token)
    with db_lock, extra_db() as conn:
        rows = conn.execute(
            "SELECT * FROM audit_log ORDER BY id DESC LIMIT ?", (limit,)
        ).fetchall()
    return {"items": [dict(r) for r in rows]}

@app.get("/api/v5/export/orders.csv")
def export_orders():
    from fastapi.responses import StreamingResponse
    with db_lock, db() as conn:
        rows = conn.execute(
            "SELECT order_id,user_id,pickup_time,total_price,status,cell_number,created_at FROM orders ORDER BY order_id"
        ).fetchall()
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["order_id","user_id","pickup_time","total_price","status","cell_number","created_at"])
    writer.writerows([tuple(r) for r in rows])
    buf.seek(0)
    return StreamingResponse(
        iter([buf.getvalue()]),
        media_type="text/csv; charset=utf-8",
        headers={"Content-Disposition": "attachment; filename=neti_food_orders.csv"}
    )

@app.get("/api/v7/system")
def v7_system():
    """Compact diagnostics endpoint for demo/defense and hardware integration."""
    with db_lock, db() as main, extra_db() as extra:
        main_orders = int(main.execute("SELECT COUNT(*) c FROM orders").fetchone()["c"])
        ready = int(main.execute("SELECT COUNT(*) c FROM orders WHERE status=?", (OrderStatus.READY.value,)).fetchone()["c"])
        users = int(extra.execute("SELECT COUNT(*) c FROM users").fetchone()["c"])
        unread = int(extra.execute("SELECT COUNT(*) c FROM notifications WHERE read=0").fetchone()["c"])
    locker = locker_status()
    return {
        "app": APP_TITLE,
        "version": APP_VERSION,
        "status": "operational",
        "orders": main_orders,
        "ready_orders": ready,
        "users": users,
        "unread_notifications": unread,
        "lockers": {"total": locker["total"], "free": locker["free"], "occupied": locker["occupied"]},
        "hardware": "serial" if serial else "simulation",
        "db": {"main": str(DB_PATH), "extra": str(NETI_EXTRA_DB)},
        "generated_at": now_iso(),
    }


@app.get("/api/v7/queue")
def v7_queue():
    """Operational queue picture used by the kitchen/demo dashboard."""
    with db_lock, db() as conn:
        rows = conn.execute(
            "SELECT status, COUNT(*) c FROM orders WHERE status IN (?,?,?) GROUP BY status",
            (OrderStatus.PAID.value, OrderStatus.COOKING.value, OrderStatus.READY.value)
        ).fetchall()
    counts = {r["status"]: int(r["c"]) for r in rows}
    active = counts.get(OrderStatus.PAID.value, 0) + counts.get(OrderStatus.COOKING.value, 0)
    eta = min(30, max(1, round(active * KITCHEN_PREP_SECONDS_PER_ORDER / 60)))
    return {
        "paid": counts.get(OrderStatus.PAID.value, 0),
        "cooking": counts.get(OrderStatus.COOKING.value, 0),
        "ready": counts.get(OrderStatus.READY.value, 0),
        "active": active,
        "estimated_wait_min": eta,
        "target_wait_min": TARGET_WAIT_MIN,
        "baseline_wait_min": BASELINE_QUEUE_WAIT_MIN,
        "generated_at": now_iso(),
    }


@app.get("/api/v6/info")
def v6_info():
    return {
        "name": "NETI_Food",
        "version": APP_VERSION,
        "build": "2026.09",
        "edition": "MEGA",
        "features": [
            "server-side pricing", "atomic stock reservation", "pickup validation",
            "order timeline", "smart locker", "loyalty", "promo", "favorites",
            "reviews", "notifications", "analytics", "recommendations",
            "stock-control", "audit", "csv-export", "demo-hardware",
            "student-cashback-5-lunches-1-coffee", "queue-capacity-business-case",
        ],
    }


@app.get("/api/v6/menu/summary")
def v6_menu_summary():
    menu = menu_with_stock()
    return {
        "items": len(menu),
        "available": sum(x.stock > 0 for x in menu),
        "out_of_stock": sum(x.stock <= 0 for x in menu),
        "signature": menu_signature(menu),
        "categories": {
            c.value: sum(x.category == c for x in menu) for c in FoodCategory
        },
    }


@app.get("/api/v6/recommendations")
def v6_recommendations(request: Request, user_id: int = Query(..., ge=1), limit: int = Query(8, ge=1, le=30)):
    require_same_user(request, user_id)
    ensure_user(user_id)
    with db_lock, extra_db() as conn:
        favorite_rows = conn.execute(
            "SELECT item_id FROM favorites WHERE user_id=?", (user_id,)
        ).fetchall()
        favorite_ids = {int(r["item_id"]) for r in favorite_rows}
        review_rows = conn.execute(
            "SELECT item_id, AVG(rating) avg_rating FROM reviews GROUP BY item_id"
        ).fetchall()
        ratings = {int(r["item_id"]): float(r["avg_rating"]) for r in review_rows}
    menu = menu_with_stock()
    ranked = []
    for item in menu:
        score = recommendation_score(item, favorite_ids, set())
        score += ratings.get(item.id, 0) * 0.35
        ranked.append((score, item))
    ranked.sort(key=lambda x: (-x[0], x[1].price_rub, x[1].id))
    return {
        "user_id": user_id,
        "items": [item.model_dump() for _, item in ranked[:limit]],
        "algorithm": "favorites + availability + rating + price",
    }


@app.get("/api/v6/analytics/extended")
def v6_extended_analytics():
    with db_lock, db() as conn:
        daily = conn.execute("""
            SELECT date(created_at) day, COUNT(*) orders, ROUND(SUM(total_price),2) revenue
            FROM orders GROUP BY date(created_at) ORDER BY day DESC LIMIT 30
        """).fetchall()
        popular = conn.execute("""
            SELECT items_summary, COUNT(*) count
            FROM orders GROUP BY items_summary ORDER BY count DESC LIMIT 10
        """).fetchall()
    return {
        "daily": [dict(r) for r in daily],
        "popular_order_combinations": [dict(r) for r in popular],
        "generated_at": now_iso(),
    }


@app.post("/api/v6/admin/stock/batch")
def v6_stock_batch(payload: StockBatchUpdate):
    require_admin(payload.token)
    with db_lock, db() as conn:
        for entry in payload.items:
            get_menu_item(entry.item_id)
            conn.execute(
                "INSERT INTO menu_stock(item_id,stock) VALUES(?,?) "
                "ON CONFLICT(item_id) DO UPDATE SET stock=excluded.stock",
                (entry.item_id, entry.stock),
            )
    audit("admin", "STOCK_BATCH_UPDATE", f"count={len(payload.items)}")
    return {"ok": True, "updated": len(payload.items)}


@app.get("/api/v6/lockers/health")
def v6_lockers_health():
    occupied = occupied_cells()
    return {
        "total": LOCKER_COUNT,
        "free": len(free_cells()),
        "occupied": len(occupied),
        "utilization_percent": round(len(occupied) / LOCKER_COUNT * 100, 1),
        "cells": [
            {
                "cell_number": n,
                "mode": "hot" if n <= 4 else "cool",
                "temperature": "+60°C" if n <= 4 else "+4°C",
                "state": "occupied" if n in occupied else "free",
                "order_id": occupied[n].order_id if n in occupied else None,
            }
            for n in range(1, LOCKER_COUNT + 1)
        ],
    }


@app.get("/api/v6/users/{user_id}/dashboard")
def v6_user_dashboard(user_id: int, request: Request):
    user = auth_user(request)
    if int(user["user_id"]) != user_id: raise HTTPException(403, "Доступ запрещён")
    ensure_user(user_id, user["name"])
    orders = get_orders(user_id=user_id, limit=20)
    loyalty = get_loyalty(user_id, request)
    favorites = get_favorites(user_id, request)
    notes = notifications(user_id, request, unread_only=True)
    active = [o for o in orders if o.status != OrderStatus.COMPLETED]
    return {
        "user": loyalty,
        "active_orders": [o.model_dump() for o in active],
        "recent_orders": [o.model_dump() for o in orders[:10]],
        "favorites_count": len(favorites["items"]),
        "unread_notifications": len(notes["items"]),
        "recommendations": v6_recommendations(request, user_id, 6)["items"],
    }


@app.get("/api/v6/order/{order_id}/full")
def v6_order_full(order_id: int):
    order = get_order(order_id)
    events = order_events(order_id)
    return {
        "order": order.model_dump(),
        "events": [e.model_dump() for e in events],
        "progress": {
            "PAID": 25, "COOKING": 50, "READY": 75, "COMPLETED": 100
        }.get(order.status.value, 0),
    }

@app.get("/api/v6/cashback/{user_id}")
def v6_cashback_status(user_id: int, request: Request):
    require_same_user(request, user_id)
    """Прогресс «Студенческого кэшбэка»: 5 обедов → бесплатный кофе."""
    return get_cashback_status(user_id)


@app.post("/api/v6/cashback/{user_id}/redeem")
def v6_cashback_redeem(user_id: int, request: Request):
    """Погашение одного заработанного бесплатного кофе (показывается кассиру/бариста)."""
    user = auth_user(request)
    if int(user["user_id"]) != user_id:
        raise HTTPException(403, "Доступ запрещён")
    status = get_cashback_status(user_id)
    if status["free_coffees_available"] <= 0:
        raise HTTPException(400, "Нет доступных бесплатных кофе")
    with db_lock, extra_db() as conn:
        conn.execute(
            "UPDATE cashback_progress SET free_coffees_used = free_coffees_used + 1, updated_at=? WHERE user_id=?",
            (now_iso(), user_id),
        )
    code = f"COFFEE-{user_id}-{secrets.token_hex(3).upper()}"
    audit(str(user_id), "CASHBACK_REDEEM", code)
    return {"ok": True, "redeem_code": code, "message": "Покажите этот код на стойке выдачи, чтобы получить кофе."}


@app.get("/api/v6/analytics/capacity")
def v6_capacity_report():
    """
    Бизнес-кейс для защиты проекта: расчёт пропускной способности кухни
    и сравнение среднего времени ожидания «без UniFood» (замер, мин) и
    «с UniFood» (предзаказ + ячейка выдачи), как того требует ТЗ (п.2 и п.4).
    """
    with db_lock, db() as conn:
        rows = conn.execute(
            "SELECT pickup_time, COUNT(*) orders FROM orders GROUP BY pickup_time"
        ).fetchall()
        total_orders = conn.execute("SELECT COUNT(*) c FROM orders").fetchone()["c"]

    slots = []
    max_capacity_per_slot = max(1, (BREAK_DURATION_MIN * 60) // KITCHEN_PREP_SECONDS_PER_ORDER)
    demo_counts = {r["pickup_time"]: r["orders"] for r in rows}
    for slot in PICKUP_SLOTS:
        orders_in_slot = int(demo_counts.get(slot, 0))
        seconds_needed = orders_in_slot * KITCHEN_PREP_SECONDS_PER_ORDER
        slots.append({
            "slot": slot,
            "orders": orders_in_slot,
            "max_capacity": int(max_capacity_per_slot),
            "utilization_percent": round(orders_in_slot / max_capacity_per_slot * 100, 1) if max_capacity_per_slot else 0,
            "kitchen_time_needed_min": round(seconds_needed / 60, 1),
            "overloaded": orders_in_slot > max_capacity_per_slot,
        })

    wait_reduction_percent = round((1 - TARGET_WAIT_MIN / BASELINE_QUEUE_WAIT_MIN) * 100, 1)
    minutes_saved_per_student = BASELINE_QUEUE_WAIT_MIN - TARGET_WAIT_MIN

    return {
        "generated_at": now_iso(),
        "total_orders_recorded": total_orders,
        "assumptions": {
            "kitchen_prep_seconds_per_order": KITCHEN_PREP_SECONDS_PER_ORDER,
            "break_duration_min": BREAK_DURATION_MIN,
            "max_orders_per_break_slot": int(max_capacity_per_slot),
        },
        "slots": slots,
        "business_case": {
            "baseline_wait_minutes_without_app": BASELINE_QUEUE_WAIT_MIN,
            "target_wait_minutes_with_app": TARGET_WAIT_MIN,
            "wait_reduction_percent": wait_reduction_percent,
            "minutes_saved_per_student": minutes_saved_per_student,
            "note": (
                "Забор заказа по ячейке вместо живой очереди: студент подходит к "
                "готовому заказу по QR-коду, минуя очередь на раздаче."
            ),
        },
    }


@app.get("/favicon.ico")
def favicon():
    return Response(
        content=bytes.fromhex("000001000100010100000100200028000000160000001000000001002000000000002800000000000000000000000000000000000000000000000000"),
        media_type="image/x-icon",
    )

_PWA_ICON_CACHE: Dict[int, bytes] = {}

@app.get("/icon-180.png")
@app.get("/icon-192.png")
@app.get("/icon-512.png")
def pwa_icon(request: Request):
    """Генерирует и кэширует иконку PWA в памяти процесса."""
    try:
        from PIL import Image, ImageDraw
        image = Image.new("RGB", (512, 512), "#be123c")
        draw = ImageDraw.Draw(image)
        draw.rounded_rectangle((48, 48, 464, 464), radius=96, fill="#ffffff")
        draw.ellipse((145, 150, 367, 385), fill="#be123c")
        draw.pieslice((250, 88, 390, 220), 205, 345, fill="#166534")
        draw.line((265, 120, 305, 82), fill="#166534", width=18)
        draw.arc((180, 190, 332, 350), 10, 170, fill="#ffffff", width=14)
        size = 180 if request.url.path.endswith("180.png") else 192 if request.url.path.endswith("192.png") else 512
        cached = _PWA_ICON_CACHE.get(size)
        if cached is None:
            bio = io.BytesIO()
            image.resize((size, size)).save(bio, format="PNG", optimize=True)
            cached = bio.getvalue()
            _PWA_ICON_CACHE[size] = cached
        return Response(
            content=cached,
            media_type="image/png",
            headers={"Cache-Control": "public, max-age=604800, immutable"},
        )
    except Exception as exc:
        raise HTTPException(500, f"Не удалось создать PWA icon: {exc}")

@app.get("/manifest.webmanifest")
def manifest():
    return Response(
        content=json.dumps({
            "name": "NETI Food — НГТУ НЭТИ",
            "short_name": "NETI Food",
            "description": "Цифровая столовая НГТУ НЭТИ",
            "start_url": "/",
            "scope": "/",
            "display": "standalone",
            "display_override": ["window-controls-overlay", "standalone"],
            "background_color": "#f8fafc",
            "theme_color": "#be123c",
            "lang": "ru",
            "orientation": "any",
            "icons": [
                {"src": "/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
                {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"}
            ],
            "categories": ["food", "shopping"]
        }, ensure_ascii=False),
        media_type="application/manifest+json"
    )

@app.get("/sw.js")
def service_worker():
    return Response(content=r'''const CACHE="neti-food-shell-v11";
const SHELL=["/","/manifest.webmanifest","/icon-192.png","/icon-512.png"];
self.addEventListener("install",event=>{
  event.waitUntil(caches.open(CACHE).then(c=>c.addAll(SHELL).catch(()=>{})).then(()=>self.skipWaiting()));
});
self.addEventListener("activate",event=>{
  event.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k!==CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));
});
self.addEventListener("fetch",event=>{
  if(event.request.method!=="GET") return;
  const u=new URL(event.request.url);
  if(u.origin!==location.origin) return;
  if(u.pathname.startsWith("/api/")) return;
  const isDocument = event.request.mode === "navigate" || u.pathname === "/";
  if (isDocument) {
    event.respondWith(
      fetch(event.request).then(response=>{
        const copy=response.clone();
        caches.open(CACHE).then(c=>c.put(event.request,copy));
        return response;
      }).catch(()=>caches.match(event.request).then(c=>c || caches.match("/")))
    );
    return;
  }
  event.respondWith(
    caches.match(event.request).then(cached=>cached || fetch(event.request).then(response=>{
      const copy=response.clone();
      caches.open(CACHE).then(c=>c.put(event.request,copy));
      return response;
    }).catch(()=>caches.match("/")))
  );
});
self.addEventListener("message",event=>{
  if(event.data?.type==="SKIP_WAITING") self.skipWaiting();
});
''' , media_type="application/javascript")

@app.get("/", response_class=HTMLResponse)
def serve_ui():
    return HTMLResponse(
        content=HTML,
        headers={"Cache-Control": "no-cache, must-revalidate"},
    )

def _hardware_send_led(cell_number: int, state: str = "ON") -> None:
    command = f"CELL_{state}:{cell_number}\n"
    if serial is None:
        print(f"  [СИМУЛЯЦИЯ] -> контроллер: {command.strip()}")
        return
    try:
        with serial.Serial(HARDWARE_PORT, HARDWARE_BAUD, timeout=1) as ser:
            ser.write(command.encode("utf-8"))
        print(f"  [СТЕНД] Команда отправлена на {HARDWARE_PORT}: {command.strip()}")
    except Exception as exc:
        print(f"  [СТЕНД] Порт недоступен ({exc}), показываю симуляцию: {command.strip()}")


def _cook_order_demo(order_id: int, api_base: str, pause: float = 2.0) -> None:
    import requests
    print(f"\n=== Повар начинает готовить заказ #{order_id} ===")
    r = requests.post(f"{api_base}/api/orders/{order_id}/status/cooking")
    if r.status_code != 200:
        print(f"  Ошибка: {r.status_code} {r.text}")
        return
    print("  Статус: PAID -> COOKING")
    time.sleep(pause)

    print("  Повар нажимает «Заказ готов»...")
    r = requests.post(f"{api_base}/api/orders/{order_id}/ready")
    if r.status_code != 200:
        print(f"  Ошибка: {r.status_code} {r.text}")
        return
    order = r.json()
    cell = order.get("cell_number")
    print(f"  Статус: COOKING -> READY, назначена ячейка №{cell}")
    if cell:
        _hardware_send_led(cell, "ON")
    print(f"=== Заказ #{order_id} готов к выдаче в ячейке №{cell} ===\n")


def _watch_queue_demo(api_base: str, interval: float = 5.0) -> None:
    import requests
    print("Слежу за очередью заказов. Ctrl+C для выхода.\n")
    seen: set[int] = set()
    try:
        while True:
            r = requests.get(f"{api_base}/api/orders", params={"status_filter": "PAID"})
            for order in r.json():
                oid = order["order_id"]
                if oid not in seen:
                    seen.add(oid)
                    print(f"Новый заказ в очереди: #{oid} ({order['items_summary']})")
                    input(f"  Нажмите Enter, чтобы повар начал готовить заказ #{oid}...")
                    _cook_order_demo(oid, api_base)
            time.sleep(interval)
    except KeyboardInterrupt:
        print("\nОстановлено.")

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="NETI_Food / UniFood — сервер и демо-инструменты")
    parser.add_argument("--cook", type=int, metavar="ORDER_ID", help="Симулировать приготовление конкретного заказа и выход")
    parser.add_argument("--watch", action="store_true", help="Следить за новыми заказами и предлагать готовить по одному")
    parser.add_argument("--api", default=f"http://127.0.0.1:{os.getenv('NETI_FOOD_PORT', '8000')}", help="Адрес уже запущенного backend (для --cook/--watch)")
    args = parser.parse_args()

    if args.cook:
        _cook_order_demo(args.cook, args.api)
        raise SystemExit(0)
    if args.watch:
        _watch_queue_demo(args.api)
        raise SystemExit(0)

    import uvicorn

    uvicorn.run(
        "app:app",
        host=os.getenv("NETI_FOOD_HOST", "0.0.0.0"),
        port=int(os.getenv("NETI_FOOD_PORT", "8000")),
        reload=os.getenv("NETI_FOOD_RELOAD", "0") == "1",
    )
