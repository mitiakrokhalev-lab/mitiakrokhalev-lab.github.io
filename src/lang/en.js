// АНГЛИЙСКИЙ СЛОВАРЬ.
//
// Ключ — русский текст ровно в том виде, в каком он стоит в коде или в
// разметке (см. src/lang/i18n.js). Сторож в test/lang.test.js следит, чтобы
// ключ нашёлся для КАЖДОЙ помеченной строки: перевод, отставший от правки,
// иначе обнаружился бы только у читателя — и молча, потому что непереведённое
// просто остаётся русским.
//
// ПЕРЕВОД ЗДЕСЬ — НЕ ПОДСТРОЧНИК. Это олимпиадная геометрия, и у неё свой
// английский: circumcircle, incircle, radical axis, symmedian, pole and polar,
// midpoint of arc. Переводить «описанная окружность» как «described circle»
// значит выдать себя с первой строки.
//
// Строки с подстановками хранят места НОМЕРАМИ — {1}, {2} — и номера можно
// переставлять: порядок слов в английском свой.
//
// Пока словарь покрывает только подписи интерфейса. Остальное — сообщения
// движка, пояснения в блоках «?», формулировки генератора — добавляется
// слоями, и до тех пор английский посетитель видит их по-русски. Поэтому
// русский остаётся языком по умолчанию даже для чужого браузера.
const S = '\u0001';

export const WORDS = {
  // ---- шапка ---------------------------------------------------------------
  'делайте построения — координаты точек появятся справа':
    'build something — the coordinates appear on the right',

  'панель GeoGebra': 'GeoGebra panel',
  'боковая панель GeoGebra с координатами':
    "GeoGebra's own side panel with coordinates",

  'рисовать': 'draw',
  'строить ли найденное на чертеже; выключите, если GeoGebra стала тормозить':
    'whether to draw what is found; turn this off if GeoGebra slows down',

  'сетка и оси': 'grid and axes',
  'сетка и оси GeoGebra на полотне': 'GeoGebra grid and axes on the canvas',

  // ---- вкладки -------------------------------------------------------------
  //
  // «Задачи» — это Problems, а не Tasks: в олимпиадном английском задача по
  // геометрии называется problem, и tasks прозвучало бы как список дел.
  'Генератор': 'Generator',
  'Задачи': 'Problems',
  'Чат': 'Chat',
  'Учётная запись': 'Account',

  // ---- таблица движка ------------------------------------------------------
  //
  // Названия движков (Компланатор, Бариканатор) не переводятся: это
  // придуманные имена, такие же как GeoGebra. А вот заголовок таблицы —
  // обычное слово, и по-английски «Алгебра» это Algebra, но у барицентрики
  // устоявшееся название barycentrics, а не «Barycentric».
  'Алгебра': 'Algebra',
  'Барицентрика': 'Barycentrics',
  'через a, b, c на единичной окружности': 'via a, b, c on the unit circle',
  'барицентрика относительно ABC': 'barycentrics with respect to ABC',

  'движок включён': 'engine on',
  'движок выключен': 'engine off',

  'посчитать': 'compute',
  'посчитать (Ctrl+Enter)': 'compute (Ctrl+Enter)',
  'считаю…': 'computing…',
  // Кнопка переключает вид уравнения: канонический или нормированный. Место
  // на ней узкое, поэтому и по-русски сокращено — сокращаем и здесь.
  'кан.': 'canon.',
  'норм.': 'norm.',

  // ---- панели --------------------------------------------------------------
  'генерирование теорем — по вашему построению':
    'theorem search — from your construction',
  'случайный отбор — вместо полного перебора слоя':
    'random sampling — instead of exhausting the layer',
  'ускорения поиска — по вашему выбору': 'search speed-ups — your choice',
  'генерировать': 'search',
  'случайная задача': 'random problem',
  'хватит': 'stop',
  'убрать нарисованное': 'clear what was drawn',
  'как это читать': 'how to read this',
  'сохранить задачу': 'save the problem',
  'получить решение': 'get the solution',
  'нарисовать ГМТ': 'draw the locus',
  'чат': 'chat',
  'учётная запись': 'account',

  'командная строка — по системе на строку':
    'command line — one system per line',
  'выполнить (Ctrl+Enter)': 'run (Ctrl+Enter)',
  'какие есть команды': 'available commands',
  'выражения от координат — по выражению на строку':
    'expressions in the coordinates — one per line',
  'условие на точки — когда написанное выполняется':
    'a condition on points — when what you wrote holds',
  'получить уравнение (Ctrl+Enter)': 'get the equation (Ctrl+Enter)',
  'как этим пользоваться': 'how to use this',
  'зачем это': 'what this is for',
  'что умеет Компланатор': 'what Complanator can do',

  // ---- витрина -------------------------------------------------------------
  //
  // Первая страница, которую видит пришедший. До недавнего времени она была
  // русской целиком — включая для того, кто пришёл именно за английской
  // версией; дальше он не шёл.
  //
  // Переносы строк в ключах схлопнуты: ключ не должен зависеть от того, как
  // отступлена разметка (см. flat в i18n.js).
  'Рисуете построение в GeoGebra — рядом появляется <b>точная координата</b> каждой точки: не «(1.73, 0.42)», а выражение через вершины треугольника.':
    'You draw a construction in GeoGebra, and next to it appears the <b>exact coordinate</b> of every point: not “(1.73, 0.42)”, but an expression in the vertices of the triangle.',
  'считает браузер · ставить ничего не нужно · бесплатно':
    'runs in your browser · nothing to install · free',

  'Открыть Крополятор': 'Open Kropolyator',
  'Скачать одним файлом': 'Download as a single file',
  'Инструкция': 'Manual',

  'Что он делает': 'What it does',
  'Поставьте три свободные точки — это <code>A</code>, <code>B</code>, <code>C</code>, их описанная окружность считается единичной. Дальше стройте что угодно: середины, перпендикуляры, касательные, инцентр. Каждый построенный объект тут же получает свою запись.':
    'Place three free points — these are <code>A</code>, <code>B</code>, <code>C</code>, and their circumcircle is taken to be the unit circle. Then build whatever you like: midpoints, perpendiculars, tangents, the incenter. Every object you construct immediately gets its own expression.',
  'Дальше с этим можно работать: проверить своё утверждение, найти, при каком условии оно выполняется, или попросить генератор поискать теоремы на вашем чертеже.':
    'From there you can work with it: check a claim of your own, find the condition under which it holds, or ask the generator to look for theorems in your figure.',

  'Три движка': 'Three engines',
  'Комплексные числа: вершины на единичной окружности, координата — выражение через <code>a, b, c</code>. Проверяет утверждения точно: «выполняется всегда» означает доказано, а не «сошлось на этом чертеже».':
    'Complex numbers: the vertices lie on the unit circle, and a coordinate is an expression in <code>a, b, c</code>. Claims are checked exactly: “always true” means proved, not “it matched on this picture”.',
  'Барицентрика: однородная тройка над длинами сторон. Там, где комплексные числа буксуют (всё, что про длины и площади), считает он.':
    'Barycentrics: a homogeneous triple over the side lengths. Where complex numbers stall — anything about lengths and areas — this engine does the work.',
  'Генератор теорем': 'Theorem generator',
  'Достраивает ваш чертёж и ищет на нём верные утверждения, отсеивая то, что следует из построения, доказывается векторами или стоит в учебнике.':
    'It extends your figure and searches it for true statements, discarding what follows from the construction, what vectors settle, and what already stands in the textbook.',
  'Бариканатор и генератор — платные: 150 ₽ за месяц доступа к каждому. Компланатор бесплатен и останется бесплатным. Заведите учётную запись прямо в приложении.':
    'Barikanator and the generator are paid: 150 ₽ for a month of access to each. Complanator is free and will stay free. Create an account inside the app.',

  'Ещё': 'More',
  '<b>Неравенства и тождества.</b> Ищет точные границы между величинами чертежа — длинами, расстояниями, площадями, углами.':
    '<b>Inequalities and identities.</b> It finds sharp bounds between the quantities of a figure — lengths, distances, areas, angles.',
  '<b>Задачи на ГМТ.</b> Одна точка едет, остальные стоят: что при этом не меняется.':
    '<b>Locus problems.</b> One point moves, the rest stay put: what remains unchanged.',
  '<b>Выгрузка.</b> Условие словами, чертёж и протокол расчёта — одним файлом, который открывается двойным кликом и печатается как есть.':
    '<b>Export.</b> The statement in words, the figure and the computation log — in one file that opens with a double click and prints as it is.',
  '<b>Работает с телефона</b> и без сети: скачанный файл считает сам, только чертёж приходит от GeoGebra.':
    '<b>Works on a phone</b> and offline: the downloaded file computes on its own, only the figure comes from GeoGebra.',

  // Футер: обещание про «ничего никуда не отправляется» убрано, добавлены
  // оферта и реквизиты — их ищет и проверяющий платёжного сервиса, и
  // покупатель. Адреса страниц кириллические и переводу не подлежат.
  'Крополятор · <a href="https://github.com/mitiakrokhalev-lab/mitiakrokhalev-lab.github.io">исходники</a> · <a href="./оферта.html">оферта</a> · <a href="./реквизиты.html">реквизиты</a>':
    'Kropolyator · <a href="https://github.com/mitiakrokhalev-lab/mitiakrokhalev-lab.github.io">source</a> · <a href="./оферта.html">terms</a> · <a href="./реквизиты.html">seller details</a>',

  // ---- панель генератора: чем достраивать ----------------------------------
  //
  // Названия построений и пояснения к ним лежат в ops.js, рядом с самими
  // операциями, и панель берёт их оттуда. Переводятся они здесь, а
  // оборачивает их t() в app.js — сам движок при этом не трогается.
  //
  // Это та половина текста, из-за которой интерфейс выглядел смесью: шапка и
  // вкладки были английскими, а вся колонка «чем достраивать» — русской.
  'прямые': 'lines',
  'точки': 'points',
  'окружности': 'circles',
  'пересечения (идут в конце слоя)': 'intersections (built last in the layer)',
  'центры треугольника': 'triangle centers',
  'Шалтай, Болтай и касания': 'Humpty, Dumpty and tangency points',
  'сопряжения, прямые, окружность девяти точек':
    'conjugates, lines, the nine-point circle',
  'полный четырёхсторонник': 'complete quadrilateral',

  'прямая через две точки': 'line through two points',
  'перпендикуляр из точки к прямой': 'perpendicular from a point to a line',
  'прямая через точку, параллельная данной':
    'line through a point parallel to a given one',
  'серединный перпендикуляр к отрезку': 'perpendicular bisector of a segment',
  'биссектриса угла': 'angle bisector',
  'внешняя биссектриса угла': 'external angle bisector',
  'отражение прямой относительно прямой': 'reflection of a line in a line',
  'касательная к окружности через три точки в первой из них':
    'tangent to the circle through three points, at the first of them',
  'поляра точки (для точки на окружности — касательная в ней)':
    'polar of a point (for a point on the circle, the tangent at it)',
  'радикальная ось двух окружностей': 'radical axis of two circles',
  'середина отрезка': 'midpoint of a segment',
  'основание перпендикуляра из точки на прямую':
    'foot of the perpendicular from a point to a line',
  'отражение точки относительно прямой': 'reflection of a point in a line',
  'симметрия точки относительно точки': 'reflection of a point in a point',
  'центр окружности': 'center of a circle',
  'инверсия точки относительно окружности': 'inverse of a point in a circle',
  'достроение треугольника до параллелограмма':
    'completing a triangle to a parallelogram',
  'достроение треугольника до равнобедренной трапеции':
    'completing a triangle to an isosceles trapezoid',
  'ортоцентр треугольника': 'orthocenter of a triangle',
  'окружность через три точки': 'circle through three points',
  'окружность по центру и точке на ней': 'circle by its center and a point on it',
  'вписанная в треугольник окружность': 'incircle of a triangle',
  'вневписанная окружность против первой вершины':
    'excircle opposite the first vertex',
  'окружность, вписанная в сегмент': 'circle inscribed in a segment',
  'полувписанная окружность в угле первой вершины':
    'mixtilinear incircle in the angle at the first vertex',
  'пересечение двух прямых': 'intersection of two lines',
  'точка касания прямой и окружности': 'point of tangency of a line and a circle',
  'второе пересечение прямой и окружности (первая точка известна)':
    'second intersection of a line and a circle (the first point is known)',
  'второе пересечение двух окружностей (первая точка известна)':
    'second intersection of two circles (the first point is known)',
  'отражение окружности относительно прямой': 'reflection of a circle in a line',
  'отражение окружности относительно точки': 'reflection of a circle in a point',
  'отражение прямой относительно точки': 'reflection of a line in a point',
  'образ окружности при инверсии': 'image of a circle under inversion',
  'образ окружности через центр инверсии — прямая':
    'image of a circle through the center of inversion — a line',
  'образ прямой при инверсии': 'image of a line under inversion',
  'перенос прямой на вектор': 'translation of a line by a vector',
  'перенос окружности на вектор': 'translation of a circle by a vector',
  'окружность с центром и радиусом-отрезком':
    'circle with a given center and a segment as radius',
  'окружность на отрезке как на диаметре': 'circle with a segment as diameter',

  // Пояснения к построениям. «Аргументы (A, B, C) — …» становится
  // «Arguments (A, B, C): …»: тире в английском здесь не читается.
  'Аргументы (A, B, C) — биссектриса угла ABC, то есть при вершине B.':
    'Arguments (A, B, C): the bisector of angle ABC, that is, at the vertex B.',
  'Аргументы (A, B, C) — внешняя биссектриса угла ABC.':
    'Arguments (A, B, C): the external bisector of angle ABC.',
  'Прямые должны пересекаться; у параллельных биссектрисы нет.':
    'The lines must meet; parallel lines have no bisector.',
  'Аргументы (l, m) — образ l при отражении относительно m.':
    'Arguments (l, m): the image of l reflected in m.',
  'Аргументы (A, B, C) — касательная в A к окружности ABC.':
    'Arguments (A, B, C): the tangent at A to circle ABC.',
  'Аргументы (P, O) — образ P при симметрии с центром O.':
    'Arguments (P, O): the image of P under the half-turn about O.',
  'Аргументы (P, O) — образ P при повороте вокруг O.':
    'Arguments (P, O): the image of P rotated about O.',
  'Аргументы (A, B, C) — четвёртая вершина, противоположная B.':
    'Arguments (A, B, C): the fourth vertex, opposite B.',
  'Аргументы (A, B, C) — отражение C относительно серединного перпендикуляра к AB.':
    'Arguments (A, B, C): the reflection of C in the perpendicular bisector of AB.',
  'Аргументы (O, P) — центр и точка на окружности; порядок существен.':
    'Arguments (O, P): the center and a point on the circle; the order matters.',
  'Аргументы (A, B, C) — окружность, касающаяся BC и продолжений AB, AC.':
    'Arguments (A, B, C): the circle tangent to BC and to the extensions of AB and AC.',
  'Аргументы (A, B, C) — окружность, касающаяся хорды BC и дуги описанной ABC в точке A.':
    'Arguments (A, B, C): the circle tangent to the chord BC and to the arc of circle ABC at A.',
  'Аргументы (A, B, C) — окружность, касающаяся AB, AC и описанной ABC изнутри.':
    'Arguments (A, B, C): the circle tangent to AB, AC and internally to circle ABC.',
  'Одна из двух точек пересечения. Какая именно — задаётся направлением':
    'One of the two intersection points. Which one is fixed by the direction',
  'Прямая обязана касаться окружности; вообще же это ближайшая к центру точка прямой.':
    'The line must be tangent to the circle; in general this is the point of the line nearest the center.',
  'Точка обязана лежать и на прямой, и на окружности; иначе построения нет.':
    'The point must lie on both the line and the circle; otherwise there is no construction.',
  'Точка обязана лежать на обеих окружностях.':
    'The point must lie on both circles.',
  'Аргументы (c, l) — образ c при отражении относительно l.':
    'Arguments (c, l): the image of c reflected in l.',
  'Аргументы (c, P) — образ c при симметрии относительно P.':
    'Arguments (c, P): the image of c under the half-turn about P.',
  'Аргументы (l, P) — образ l при симметрии относительно P.':
    'Arguments (l, P): the image of l under the half-turn about P.',
  'Аргументы (c, ω) — образ c при инверсии относительно ω.':
    'Arguments (c, ω): the image of c under inversion in ω.',
  'Аргументы (l, ω) — образ l при инверсии относительно ω; окружность через центр.':
    'Arguments (l, ω): the image of l under inversion in ω; a circle through the center.',
  'Аргументы (l, A, B) — образ l при переносе на вектор AB.':
    'Arguments (l, A, B): the image of l translated by the vector AB.',
  'Аргументы (c, A, B) — образ c при переносе на вектор AB.':
    'Arguments (c, A, B): the image of c translated by the vector AB.',
  'Аргументы (O, A, B) — окружность с центром O радиуса AB.':
    'Arguments (O, A, B): the circle centered at O with radius AB.',
  'Аргументы (A, B) — окружность с диаметром AB.':
    'Arguments (A, B): the circle with diameter AB.',
  'Аргументы (P, O) — образ P при гомотетии с центром O.':
    'Arguments (P, O): the image of P under the homothety centered at O.',
  'Аргументы (l, O) — образ l при гомотетии с центром O.':
    'Arguments (l, O): the image of l under the homothety centered at O.',
  'Аргументы (c, O) — образ c при гомотетии с центром O.':
    'Arguments (c, O): the image of c under the homothety centered at O.',
  'Аргументы (l, O) — образ l при повороте вокруг O.':
    'Arguments (l, O): the image of l rotated about O.',
  'Аргументы (c, O) — образ c при повороте вокруг O.':
    'Arguments (c, O): the image of c rotated about O.',
  'Аргумент (O) — центр окружности.': 'Argument (O): the center of the circle.',

  // ---- что искать ----------------------------------------------------------
  'точки на одной прямой': 'points on one line',
  'точки на одной окружности': 'points on one circle',
  'прямые через одну точку': 'lines through one point',
  'параллельность': 'parallelism',
  'перпендикулярность': 'perpendicularity',
  'равенство отрезков': 'equal segments',
  'равенство углов': 'equal angles',
  'касание прямой и окружности': 'tangency of a line and a circle',
  'касание окружностей': 'tangency of circles',
  'точка на прямой': 'point on a line',
  'окружности через одну точку': 'circles through one point',
  'совпадение разных построений': 'coincidence of different constructions',

  // ---- подписи полей в панели ----------------------------------------------
  'что видит генератор': 'what the generator sees',
  'что доказать': 'what to prove',
  'взаимозаменяемые объекты': 'interchangeable objects',
  'условная теорема — искать следствия посылки':
    'conditional theorem — look for consequences of a premise',
  'задача на ГМТ — одни точки стоят, другие ездят':
    'locus problem — some points stay put, others move',
  'геометрические неравенства — искать точные оценки':
    'geometric inequalities — look for sharp bounds',
  'тождества — соотношения, отношения, значения углов':
    'identities — relations, ratios, angle values',
  'посылку придумает генератор': 'let the generator invent the premise',
  'с какой точки начинать (можно не заполнять)':
    'which point to start from (may be left empty)',
  'подвижные точки (пусто — выберет генератор)':
    'moving points (empty — the generator chooses)',
  'одна из точек — ключевая': 'one of the points is the key one',

  'слоёв достраивания': 'layers of extension',
  'глубина достройки': 'depth of extension',
  'объектов на слой': 'objects per layer',
  'потолок мира, объектов': 'ceiling of the world, objects',
  'конфигураций': 'configurations',
  'сколько готовы ждать, секунд': 'how long you are willing to wait, seconds',
  'включить случайный отбор': 'enable random sampling',
  'наборов': 'sets',
  'точек в наборе': 'points per set',
  'зерно': 'seed',
  'Лимит': 'Limit',
  'в точности столько': 'exactly this many',
  'трёхточечные построения — по всем точкам':
    'three-point constructions — over all points',
  'Точки в величины идут только нарисованные':
    'Only drawn points go into quantities',
  'Величины строятся по тройкам и четвёркам точек':
    'Quantities are built from triples and quadruples of points',

  'проверка найденного': 'checking what was found',
  'Без проверки': 'No check',
  'Быстрая': 'Quick',
  'Полная': 'Full',
  'узнаётся ли постоянная': 'whether the constant is recognized',
  'счёт: пока нечего мерить': 'count: nothing to measure yet',
  'инициализация…': 'starting up…',
  'Условия области появятся здесь после первого прогона.':
    'The conditions of the region will appear here after the first run.',

  'Галочка стоит:': 'Checked:',
  'Галочка снята (так по умолчанию):': 'Unchecked (the default):',
  'По чему ездить, решаете вы, а не чертёж.':
    'What moves is your decision, not the figure’s.',
  'Половина неравенств верна не везде, а на области.':
    'Half of all inequalities hold not everywhere, but on a region.',
  'Проверка — самая дорогая стадия и самое разборчивое сито.':
    'Checking is the most expensive stage and the most selective sieve.',
  'Сито тут своё.': 'The sieve here is its own.',
  'отказ от целого класса задач': 'giving up a whole class of problems',

  'движок выключен: построенное сейчас в таблицу не попадёт и останется невидимым для него даже после включения':
    'engine off: what you build now will not enter the table and stays invisible to it even after you switch the engine back on',
  'Условие собирается по вашему построению, чертёж — снимком полотна. Получается один файл: открыть двойным кликом, распечатать, отправить.':
    'The statement is assembled from your construction, the figure from a snapshot of the canvas. The result is a single file: open it with a double click, print it, send it.',
  'Для «сохранить задачу» годится любая фраза — она просто попадёт в условие. Для «получить решение» пишите на языке движка, как в блоке «условие на точки»: тогда утверждение будет проверено, а не переписано.':
    'For “save the problem” any wording will do — it simply goes into the statement. For “get the solution” write in the engine’s language, as in the “a condition on points” block: then the claim is checked, not merely copied.',
  'Нарисуйте три свободные точки — это будут A, B, C (⇒ a, b, c), описанная окружность считается единичной. Дальше стройте что угодно — строки появятся автоматически. Точки сверх трёх тоже можно: произвольная точка плоскости получит букву d и независимую d̄, а посаженная на окружность или прямую — своё правило сопряжения.':
    'Draw three free points — they become A, B, C (⇒ a, b, c), and their circumcircle is taken to be the unit circle. Then build whatever you like: the rows appear by themselves. More than three points is fine as well: an arbitrary point of the plane gets the letter d and an independent d̄, while a point placed on a circle or a line gets its own conjugation rule.',

  // ---- сообщения -----------------------------------------------------------
  //
  // Это сообщение обречено показываться по-русски: до него доходит только
  // тогда, когда словарь НЕ загрузился. Перевод всё равно нужен — на случай,
  // когда английский уже выбран, а обратное переключение не удалось.
  'словарь не загрузился — остаёмся на русском':
    'the dictionary did not load — staying in Russian',
};

// S пригодится первой же строке с подстановкой: ключ такой строки собирается
// как ['величин ' + S + ' из ' + S], а значением идёт 'ЕЁ ПЕРЕВОД С {1} И {2}'.
// Пока таких строк нет, и это нормально: подписи кнопок обходятся без них.
export const SLOT_FOR_TEMPLATES = S;
