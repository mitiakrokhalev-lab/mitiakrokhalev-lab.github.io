import { Ring } from '../symbolic/ring.js';
import { LineEq } from '../symbolic/line.js';
import { CircleEq } from '../symbolic/circle.js';
import { ConicEq } from '../symbolic/conic.js';
import { lineMeetsCircle, circlesMeet, lineMeetsCircleExtended,
  adjoinBySumAndProduct } from '../symbolic/quadratic.js';
import { parseProgram, solveSystem, conditionEquations, kindOf } from '../symbolic/constraints.js';
import { byPowers, realPoly, denormPoly, polyCommand, orderOf, conicKind,
         parseImplicit, normPoly, toZBar } from '../symbolic/locus.js';

// Таблица одночленов → коэффициенты коники: conicKind ждёт именно их.
const fromMap = m => ({
  xx: m.get('2,0') ?? 0, xy: m.get('1,1') ?? 0, yy: m.get('0,2') ?? 0,
  x: m.get('1,0') ?? 0, y: m.get('0,1') ?? 0, one: m.get('0,0') ?? 0,
});
import { implicitize } from '../symbolic/eliminate.js';
import { evaluateLine, evalAst } from '../symbolic/expression.js';
import { fullyFactored } from '../symbolic/rational.js';
import { F } from '../symbolic/formulas.js';
import { rootOfUnity } from '../symbolic/unity.js';
import { QuadraticExt } from '../symbolic/quadratic-ext.js';
import { CFrac } from '../symbolic/complex-fraction.js';
import { Fraction } from '../symbolic/fraction.js';
import { C, circumFrame, distanceToLine, nearestIndex } from './numeric.js';
import { rationalToGgb, valueToGgb, isDrawableValue } from './ggb-expression.js';
import { withFactorBudget, withComputeBudget, BudgetExceeded, CeilingExceeded } from '../symbolic/gcd.js';

// Воспроизводимый источник случайностей для разложения: разделение равных
// степеней без случайности не работает, но два одинаковых запроса обязаны дать
// одинаковый ответ.
function makeSeededRandom(seed) {
  let s = (seed >>> 0) || 1;
  return n => {
    s = (Math.imul(s, 1103515245) + 12345) & 0x7fffffff;
    return s % n;
  };
}

// Служебные объекты, которыми мы переводим чертёж в систему координат движка.
// Мост их пропускает, иначе они попали бы в таблицу как обычные построения.
const AUX_PREFIX = 'cmpl';

// Насколько символьный ответ вправе расходиться с реальными координатами
// на чертеже. Координаты приходят из GeoGebra уже в double, плюс нормировка —
// поэтому порог не машинный.
const CHECK_TOLERANCE = 1e-6;
// Выше этого масштаба точка на чертеже считается ушедшей в бесконечность.
const DEGENERATE_SCALE = 1e8;

// Почему уравнение не решилось — человеческим языком.
const QUADRATIC_EXCUSE = {
  irrational: 'нужны радикалы: ни одна из построенных точек не оказалась корнем, '
    + 'а извлекать корень из дискриминанта движок не умеет',
  degenerate: 'уравнение выродилось: объекты совпадают или не пересекаются',
};

// Первые три свободные точки — вершины треугольника, они и задают описанную
// окружность как единичную. Дальше буквы для произвольных точек: без i (мнимая
// единица), без o (путается с нулём), без z (это неизвестная в уравнениях).
const TRIANGLE_LETTERS = ['a', 'b', 'c'];
const EXTRA_LETTERS = 'defghklmnpqrstuvw'.split('');

// getObjectType отдаёт НЕ класс объекта, а его человеческое имя в нижнем
// регистре (GgbAPI#getObjectType → GeoElement#getTypeString). У многоугольника
// это зависит от числа вершин: "polygon" приходит только с семиугольника,
// треугольник называется "triangle" (GeoPolygon#getTypeString).
export const POLYGON_TYPES = new Set(['polygon', 'triangle', 'quadrilateral', 'pentagon', 'hexagon']);
export const LINE_TYPES = new Set(['line', 'segment', 'ray']);
export const CIRCLE_TYPES = new Set(['circle', 'conic']);
// Коники GeoGebra называет по виду кривой; «conic» приходит у общей, а
// окружность у неё отдельным типом. Разбираем их так же, как прямые и
// окружности, — ПО КОМАНДЕ построения, а не по числовым коэффициентам: команда
// говорит, из чего кривая сделана, и через те же объекты она у нас и выражается.
export const CONIC_TYPES = new Set(['ellipse', 'hyperbola', 'parabola', 'conic']);

// GeoGebra отдаёт команду построения в двух видах:
//   getCommandString(name)        — ЛОКАЛИЗОВАННЫЙ: на русском интерфейсе это
//                                   "Перпендикуляр(A, a)", "Пересечение(f, g)";
//   getCommandString(name, false) — ВНУТРЕННИЙ: "OrthogonalLine[A,a]",
//                                   "Intersect[f,g]" — не зависит от языка, но
//                                   в КВАДРАТНЫХ скобках и под внутренними
//                                   именами (GgbAPI#getCommandString +
//                                   StringTemplate#leftCommandBracket).
// Внутренние имена местами не совпадают с английскими из справки:
const COMMAND_ALIASES = {
  OrthogonalLine: 'PerpendicularLine',
  LineBisector: 'PerpendicularBisector',
  AngularBisector: 'AngleBisector',
  Mirror: 'Reflect',
};

// Центры треугольника (нумерация Кимберлинга), выразимые рационально через
// a, b, c при описанной окружности = единичной. X(1) (инцентр) сюда не входит:
// он зависит от длин сторон, а это радикалы.
const TRIANGLE_CENTERS = {
  2: (p, q, r) => p.add(q).add(r).div(3n),   // центроид
  3: (p, q, r) => F.circumcenter(p, q, r),   // центр описанной (= 0)
  4: (p, q, r) => p.add(q).add(r),           // ортоцентр
  5: (p, q, r) => p.add(q).add(r).div(2n),   // центр окружности девяти точек
};

function splitTopLevelArgs(s) {
  const out = [];
  let depth = 0;
  let cur = '';
  for (const ch of s) {
    if (ch === '(' || ch === '[') depth++;
    else if (ch === ')' || ch === ']') depth--;
    if ((ch === ',' || ch === ';') && depth === 0) { out.push(cur.trim()); cur = ''; continue; }
    cur += ch;
  }
  if (cur.trim()) out.push(cur.trim());
  return out;
}

// Понимает и "Cmd[x, y]" (внутренний вид), и "Cmd(x, y)" (локализованный или
// набранный руками в строке ввода).
export function parseCommand(cmdStr) {
  if (!cmdStr) return null;
  const m = String(cmdStr).trim().match(/^([A-Za-z][A-Za-z0-9_]*)\s*[([]([\s\S]*)[)\]]$/);
  if (!m) return null;
  return { name: COMMAND_ALIASES[m[1]] ?? m[1], args: splitTopLevelArgs(m[2]) };
}

// ЦИРКУЛЬ: чем задан раствор.
//
// Инструмент GeoGebra «Циркуль» пишет `Circle(A, f)`, где f — ОТРЕЗОК на
// чертеже; то же самое приходит и записями `Circle(A, Segment(B,C))` и
// `Circle(A, Distance(B,C))`. Во всех трёх случаях радиус задан ПАРОЙ ТОЧЕК, и
// это ровно то, что нужно обоим движкам: сама длина иррациональна, а её квадрат
// рационален, и окружность хранится квадратом радиуса.
//
// Разбор общий, потому что общего тут всё, кроме способа найти точку по имени, —
// его каждый движок передаёт сам.
export const isPlainNumber = arg => /^[+-]?\d+(\.\d+)?([eE][+-]?\d+)?$/.test(String(arg ?? '').trim());

export function compassEnds(arg, { segment, point }) {
  const ends = segment(arg);
  if (ends) return ends;
  const nested = parseCommand(arg);
  if (!nested || nested.args.length !== 2) return null;
  if (nested.name !== 'Segment' && nested.name !== 'Distance') return null;
  const [u, v] = nested.args.map(point);
  return u && v ? [u, v] : null;
}

// Берёт команду в независимом от языка виде, с откатом на локализованный —
// на случай старого applet, который игнорирует второй аргумент.
export function readCommand(ggbApplet, name) {
  const internal = ggbApplet.getCommandString(name, false);
  if (parseCommand(internal)) return internal;
  return internal || ggbApplet.getCommandString(name) || '';
}

// Точка, поставленная инструментом, определения не имеет вовсе. Но та же точка,
// набранная в строке ввода как A=(1,0), тоже свободна, а getCommandString
// возвращает для неё "(1, 0)" — координаты, не команду. Различает их только
// isIndependent (метод появился не сразу, поэтому проверяем наличие).
function isFreePoint(ggbApplet, name, cmd) {
  if (!cmd) return true;
  return typeof ggbApplet.isIndependent === 'function' && ggbApplet.isIndependent(name);
}

// Коэффициент гомотетии должен быть ТОЧНОЙ дробью: иррациональный вывел бы
// выражение за пределы поля, в котором работает движок. GeoGebra печатает числа
// с точностью до 13 знаков, поэтому 1/3 приходит как 0.3333333333333 — сначала
// пробуем узнать простую дробь, и только потом берём десятичную как есть.
export function parseExactRatio(text) {
  const s = String(text ?? '').trim();
  let m = s.match(/^([+-]?\d+)\s*\/\s*(\d+)$/);
  if (m) return { n: BigInt(m[1]), d: BigInt(m[2]) };
  m = s.match(/^([+-]?)(\d+)(?:\.(\d+))?$/);
  if (!m) return null;
  const sign = m[1] === '-' ? -1n : 1n;
  const frac = m[3] ?? '';
  if (frac.length === 0) return { n: sign * BigInt(m[2]), d: 1n };

  const value = Number(s);
  // цепные дроби: ищем короткую дробь, совпадающую с точностью до 1e-9
  let [h0, h1, k0, k1] = [0n, 1n, 1n, 0n];
  let x = Math.abs(value);
  for (let i = 0; i < 20; i++) {
    const whole = Math.floor(x);
    [h0, h1] = [h1, BigInt(whole) * h1 + h0];
    [k0, k1] = [k1, BigInt(whole) * k1 + k0];
    // Знаменатель ограничен: у √2 ≈ 1.4142135623731 подходящая дробь 47321/33461
    // тоже совпадает до 1e-9, но это не «простое отношение», а артефакт.
    if (k1 > 0n && k1 <= 10000n && Math.abs(Number(h1) / Number(k1) - Math.abs(value)) < 1e-9) {
      return { n: (value < 0 ? -1n : 1n) * h1, d: k1 };
    }
    if (k1 > 10000n) break;
    const rest = x - whole;
    if (rest < 1e-12) break;
    x = 1 / rest;
  }
  if (frac.length > 6) return null;              // «грязное» число — не берём
  return { n: sign * BigInt(m[2] + frac), d: 10n ** BigInt(frac.length) };
}

// Угол как ДОЛЯ ПОЛНОГО ОБОРОТА: возвращает { n, d }, означающее 2π·n/d.
//
// Раньше здесь принимались только кратные 90°, потому что e^{iα} обязано лежать
// в поле, а из таких чисел в Q(i) есть ровно четыре. Теперь поле можно
// расширить: e^{2πi·n/d} — это ζ_d^n, и он строится, когда правильный
// d-угольник строится циркулем и линейкой (см. unity.js). Так что вопрос
// «какой угол понятен» перестал быть вопросом реализации и стал вопросом
// математики — ровно как и должно быть.
//
// Дробь обязана быть НЕСОКРАТИМОЙ: иначе 180° пришло бы как 2/4 и потребовало
// бы ζ₄ там, где хватает −1, а 120° как 120/360 — ζ₃₆₀ вместо ζ₃.
export function parseTurnFraction(text) {
  const s = String(text ?? '').trim();
  const deg = s.match(/^([+-]?\d+(?:\.\d+)?)\s*°$/);
  const turns = deg
    ? parseExactRatio(String(Number(deg[1]) / 360))
    : (() => {
      // Запись через π разбираем ОТДЕЛЬНО, а не подстановкой числа: «pi/3»
      // после подстановки превращается в «3.14…/3», а Number такого не ест и
      // отдаёт NaN. Прежний разбор поворота спотыкался ровно об это и брал
      // только голые числа.
      const sym = s.match(/^([+-]?)\s*(\d+(?:\.\d+)?)?\s*\*?\s*(?:π|pi)\s*(?:\/\s*(\d+(?:\.\d+)?))?$/i);
      if (sym) {
        const sign = sym[1] === '-' ? -1 : 1;
        const mul = sym[2] === undefined ? 1 : Number(sym[2]);
        const den = sym[3] === undefined ? 1 : Number(sym[3]);
        if (!den) return null;
        return parseExactRatio(String(sign * mul / (2 * den)));
      }
      const value = Number(s);
      if (!Number.isFinite(value)) return null;
      return parseExactRatio(String(value / (2 * Math.PI)));
    })();
  if (!turns || turns.d === 0n) return null;
  const g = bigGcd(turns.n < 0n ? -turns.n : turns.n, turns.d);
  if (g === 0n) return { n: 0n, d: 1n };
  return { n: turns.n / g, d: turns.d / g };
}

function bigGcd(a, b) {
  let [x, y] = [a < 0n ? -a : a, b < 0n ? -b : b];
  while (y) [x, y] = [y, x % y];
  return x;
}

// Целая степень значения кольца: отрицательная означает обратный поворот.
function powerOf(value, e) {
  if (e === 0) return value.ring.one();
  const base = e < 0 ? value.inv() : value;
  let acc = base;
  for (let k = 1; k < Math.abs(e); k++) acc = acc.mul(base);
  return acc;
}

// Поворот остаётся в Q(i) только на углы, кратные 90°.
export function parseQuarterTurns(text) {
  const s = String(text ?? '').trim();
  const deg = s.match(/^([+-]?\d+(?:\.\d+)?)\s*°$/);
  if (deg) {
    const value = Number(deg[1]);
    return value % 90 === 0 ? Math.round(value / 90) : null;
  }
  const value = Number(s.replace(/π|pi/gi, String(Math.PI)));
  if (!Number.isFinite(value)) return null;
  const quarters = value / (Math.PI / 2);
  return Math.abs(quarters - Math.round(quarters)) < 1e-9 ? Math.round(quarters) : null;
}

// Грубая оценка ожидания по размеру самого большого промежуточного многочлена.
//
// Точной формулы тут быть не может: стоимость НОДа зависит не только от числа
// членов, но и от степеней и от того, сошлась ли эвристика. Зато порядок
// величины предсказывается — замеры на реальных задачах давали сотни членов за
// секунды, тысячи за десятки секунд. Поэтому и говорим порядок, а не число:
// выдуманная точность хуже честного «примерно».
export function estimateWait(peak) {
  if (!peak) return 'сколько — неизвестно';
  if (peak < 400) return 'скорее всего секунды';
  if (peak < 2000) return 'скорее всего десятки секунд';
  if (peak < 10000) return 'скорее всего минуты';
  return 'возможно, очень долго';
}

// Drives the symbolic engine from GeoGebra construction events.
// `onRow(name, {kind, text, tex, note, raw})` is called whenever a row should be
// added/updated; `onRemove(name)` when an object is deleted.
export class ComplanatorBridge {
  constructor({ onRow, onRemove }) {
    this.onRow = onRow;
    this.onRemove = onRemove;
    // Режим 2 — «Компланатор выключен»: строить можно что угодно, движок на это
    // не смотрит. Список выключенных объектов переживает пересборку кольца:
    // иначе после удаления вершины они молча вернулись бы в таблицу.
    this.mode = 1;
    this.ignored = new Set();
    this.#reset();
  }

  // 1 — обычная работа, 2 — движок выключен. Всё, что построено в режиме 2,
  // остаётся невидимым для него и после возврата в режим 1: иначе объект вдруг
  // получил бы букву, а его дети — уже нет.
  setMode(mode) { this.mode = mode === 2 ? 2 : 1; }

  // Рисовать ли найденное на чертеже.
  //
  // Считает движок быстро — счёт целой цепочки укладывается в сотни
  // миллисекунд. А вот GeoGebra, получив от нас объект, пересчитывает его на
  // каждое обновление чертежа, и на длинных цепочках («касательная → точка на
  // ней → прямая через неё → её пересечение») встаёт уже она сама. Наш бюджет
  // туда не дотягивается: там считает чужой код.
  //
  // Поэтому — переключатель. Выключил рисование: формулы в таблице считаются и
  // показываются как обычно, а чертёж остаётся ровно таким, каким его сделал
  // пользователь. Для разбора задачи этого чаще всего и достаточно.
  setDrawing(on) { this.drawing = on !== false; }

  #reset() {
    this.ring = new Ring();
    this.tooSlow?.clear();
    this.pointExpr = new Map();   // name -> Rational
    this.generators = new Map();  // name -> Rational (образующая, создаётся один раз)
    this.lineDefs = new Map();    // name -> { p, q, eq: LineEq }
    // Тип прямой по версии GeoGebra: line, segment или ray. Уравнение у всех
    // трёх одно и то же, а вот ClosestPoint на отрезке ведёт себя иначе.
    this.lineKind = new Map();
    this.circleDefs = new Map();  // name -> CircleEq
    this.conicDefs = new Map();   // name -> ConicEq
    this.polyDefs = new Map();    // name -> [имена вершин]
    this.freeOrder = [];          // свободные точки в порядке появления
    this.unitObjects = [];        // имена трёх вершин — по ним строится нормировка
    this.varSource = [];          // индекс образующей -> { obj, conj }
    this.usedLetters = new Set();
    // Буква точки локуса — одна на все локусы сразу. От неё пишется
    // уравнение, и никто, кроме самого уравнения, на неё не ссылается: заводить
    // по букве на каждый локус незачем, а букв конечное число.
    this.locusVar = -1;
    // Готовые уравнения локусов: имя → { value, curve }. Результант на каждое
    // движение мыши считать незачем — от перетаскивания выражение точки не
    // меняется, меняются только числа, которые в него подставляют.
    this.locusCache = new Map();
    this.rowNames = new Set();
    // Точки, найденные решением системы из командной строки. GeoGebra видит их
    // как обычные свободные точки, поэтому мост обязан помнить, что они наши, —
    // иначе каждая съела бы новую образующую.
    this.commandPoints = new Map();
    this.auxObjects = new Set();
    // Счётчик присоединённых корней: каждому нужна своя пара служебных объектов.
    this.extCount = 0;
    // Присоединённые корни по паре пересекаемых объектов: второй клик по той же
    // паре обязан дать ВТОРОЙ корень того же уравнения, а не новое расширение.
    this.extByPair = new Map();
    // То же самое для касательных, проведённых самой GeoGebra: из внешней точки
    // их две, они приходят двумя отдельными объектами, и второй обязан получить
    // ВТОРУЮ точку касания того же уравнения (см. #tangentFromOutside).
    this.tangentByPair = new Map();
    // Все заведённые расширения — чтобы обновлять их численные корни перед
    // живой сверкой с чертежом.
    this.extensions = [];
    // Сколько миллисекунд ушло на каждый объект — для разбора зависаний.
    this.timings = new Map();
    // Рисовать ли найденное на чертеже (см. setDrawing).
    this.drawing = true;
    // Объекты, не уложившиеся в бюджет: имя → готовая строка «не посчитано».
    // Нужны, чтобы обновления чертежа не запускали безнадёжный счёт заново.
    this.tooSlow = new Map();
    // Переменные пользовательской строки. Сбрасываются вместе с кольцом:
    // выражения из выброшенного кольца использовать нельзя.
    this.userVars = new Map();
    // Прямые, построенные командной строкой (buildline, radline): у них нет
    // разбираемого определения GeoGebra, уравнение знаем только мы.
    this.commandLines = new Map();
    // Имена, выданные безымянным построениям. Помним их по тексту строки,
    // чтобы повторный запуск той же команды обновлял точку, а не плодил новые.
    this.buildNames = new Map();
    this.trace = [];
  }

  // Бюджет на счёт. Дальше него ждать бессмысленно: вкладка подвисает, а
  // пользователь не знает, считается вообще или уже нет.
  //
  // Бюджет общий на ПАЧКУ событий, а не на объект. Один щелчок по пересечению
  // порождает несколько событий подряд — сама точка, её обновления, соседи, —
  // и если дать каждому по полному бюджету, то каждое уложится, а вкладка всё
  // равно встанет на их сумму. Ровно это и происходило: пользователь ждал
  // десять секунд и получал предложение закрыть страницу, ни разу не увидев
  // «не посчитано».
  //
  // Пачкой считается всё, что пришло без заметного перерыва: события от одного
  // действия идут подряд в пределах миллисекунд, а следующее действие всегда
  // отделено хотя бы паузой на отрисовку.
  static COMPUTE_BUDGET_MS = 5000;
  // Сколько даёт одно нажатие кнопки «посчитать». Не бесконечность: см. там же.
  static EXTENDED_BUDGET_MS = 60000;
  static BURST_GAP_MS = 400;

  #burstBudget(requested) {
    if (requested !== undefined) return requested;      // явный бюджет (тесты, кнопка)
    const now = Date.now();
    if (this.burstEnd === undefined || now - this.burstTouched > ComplanatorBridge.BURST_GAP_MS) {
      this.burstEnd = now + ComplanatorBridge.COMPUTE_BUDGET_MS;
    }
    this.burstTouched = now;
    return Math.max(0, this.burstEnd - now);
  }

  handleObject(ggbApplet, name, budgetMs) {
    // Замер по объектам. Нужен не для красоты: когда вкладка встаёт, надо уметь
    // отличить «движок считает» от «GeoGebra пересчитывает свой чертёж» — иначе
    // чинишь не то место. Смотреть так: complanator.timings в консоли.
    const started = Date.now();
    try {
      return this.#handleObjectWithin(ggbApplet, name, this.#burstBudget(budgetMs));
    } finally {
      const spent = Date.now() - started;
      this.timings.set(name, spent);
      if (spent >= 1000) {
        console.warn(`[Компланатор] ${name}: ${spent} мс`);
      }
    }
  }

  #handleObjectWithin(ggbApplet, name, budgetMs) {
    // Объект, который уже не уложился в бюджет, ПОВТОРНО не считаем.
    //
    // Это оказалось важнее самого бюджета. GeoGebra шлёт обновления на каждое
    // движение мыши, и без этой памяти каждое из них честно запускало счёт
    // заново и честно сжигало полные пять секунд. Строка «не посчитано»
    // появлялась — и тут же начинался следующий пятисекундный заход, так что
    // снаружи не менялось ничего.
    //
    // Пересчёт только по явному нажатию «посчитать»: оно само вычёркивает имя
    // отсюда, а обновления чертежа — нет.
    if (this.tooSlow.has(name)) {
      this.#row(name, this.tooSlow.get(name));
      return;
    }
    if (name.startsWith(AUX_PREFIX)) return;   // наша служебная обвязка
    if (this.mode === 2) { this.ignored.add(name); return; }
    if (this.ignored.has(name)) return;
    const type = ggbApplet.getObjectType(name);
    // Один объект — одна строка — один бюджет на разложение множителей.
    withFactorBudget(() => withComputeBudget(budgetMs, () => {
      try {
        if (type === 'point') this.#handlePoint(ggbApplet, name);
        else if (LINE_TYPES.has(type)) { this.lineKind.set(name, type); this.#handleLine(ggbApplet, name); }
        else if (type === 'circle') this.#handleCircle(ggbApplet, name);
        else if (CONIC_TYPES.has(type)) this.#handleConic(ggbApplet, name);
        else if (POLYGON_TYPES.has(type)) this.#handlePolygon(ggbApplet, name);
        else if (type === 'locus') this.#handleLocus(ggbApplet, name);
        else this.#noteForeign(ggbApplet, name, type);
      } catch (e) {
        // Не уложились во время — это НЕ ошибка построения. Ответ существует,
        // просто он дорогой, и решать, ждать ли, должен пользователь: только он
        // знает, нужна ли ему эта конкретная точка настолько.
        if (e instanceof BudgetExceeded) {
          const info = {
            kind: 'pending',
            text: `не посчитано за ${(e.budgetMs / 1000).toFixed(0)} с`,
            estimate: estimateWait(e.peak),
            // Досчитать по явному нажатию — но СРОК КОНЕЧНЫЙ.
            //
            // Раньше кнопка звала счёт с бюджетом Infinity, и это была
            // единственная возможность подвесить вкладку насмерть: у движка
            // формально всё конечно, но «конечно» там означает двадцать четыре
            // шага по числам в четыреста знаков. Теперь нажатие даёт минуту, а
            // не вечность; не хватило — появляется та же кнопка, и минуту можно
            // добавить ещё раз. Решение «ждать ли дальше» остаётся за
            // пользователем, но принимается оно раз в минуту, а не однажды и
            // навсегда.
            compute: () => {
              this.tooSlow.delete(name);
              this.handleObject(ggbApplet, name, ComplanatorBridge.EXTENDED_BUDGET_MS);
            },
          };
          // Запоминаем: следующие обновления чертежа не должны запускать тот же
          // безнадёжный счёт заново.
          this.tooSlow.set(name, info);
          this.#row(name, info);
          return;
        }
        // Потолок движка — не ошибка и не «не поддержано», а честная граница:
        // показатели перестали помещаться в одночлен. Пишем это словами, без
        // слова «ошибка», иначе выглядит как поломка, которой нет.
        if (e instanceof CeilingExceeded) {
          this.#row(name, { kind: 'unsupported', text: e.message });
          return;
        }
        this.#row(name, { kind: 'unsupported', text: `ошибка: ${e.message}` });
      }
    }));
  }

  remove(ggbApplet, name) {
    // Образующую из кольца выкинуть нельзя — на неё уже могут ссылаться другие
    // выражения. Поэтому если удалили именно образующую, честнее пересобрать
    // всё построение заново: буквы перераспределятся, ничего не протухнет.
    if (this.generators.has(name) && ggbApplet) { this.rebuild(ggbApplet, name); return; }
    this.#forget(name);
    this.onRemove(name);
    this.rowNames.delete(name);
  }

  #forget(name) {
    // СЛЕД ТОЖЕ ЧИСТИТСЯ.
    //
    // След читает генератор, и удалённый объект оставался в нём навсегда:
    // человек стирал с чертежа полуокружность, а генератор всё жаловался на
    // неё и строил задачу по объектам, которых на чертеже уже нет.
    this.trace = this.trace.filter(t => t?.name !== name);
    this.tooSlow.delete(name);
    this.pointExpr.delete(name);
    this.commandLines.delete(name);
    this.ignored.delete(name);
    this.commandPoints.delete(name);
    this.generators.delete(name);
    this.lineDefs.delete(name);
    this.circleDefs.delete(name);
    this.polyDefs.delete(name);
    const idx = this.freeOrder.indexOf(name);
    if (idx >= 0) this.freeOrder.splice(idx, 1);
  }

  // Полный пересчёт по текущему состоянию построения. getAllObjectNames отдаёт
  // объекты в порядке построения (Construction#getGeoSetConstructionOrder),
  // так что родители всегда встречаются раньше детей.
  rebuild(ggbApplet, skipName = null) {
    for (const n of this.rowNames) this.onRemove(n);
    this.#reset();
    const names = typeof ggbApplet.getAllObjectNames === 'function'
      ? ggbApplet.getAllObjectNames() : [];
    for (const n of names) {
      if (n && n !== skipName) this.handleObject(ggbApplet, n);
    }
  }

  #row(name, info) {
    this.rowNames.add(name);
    this.onRow(name, info);
  }

  // ЛОКУС GEOGEBRA — уравнением, а не путём.
  //
  // У встроенного локуса уравнения нет: это ломаная из точек, и алгебре точек
  // сказать о нём нечего. Уравнение даёт команда LocusEquation — неявной
  // кривой, — и вот её строку мы разбираем и переводим в наши нормированные
  // координаты, а потом в запись через z и z̄.
  //
  // Числа при этом приближённые, и точными они не станут: GeoGebra считает
  // локус численно. Поэтому строка помечается как численная — чтобы никто не
  // принял её за точный ответ движка.
  #handleLocus(ggbApplet, name) {
    if (typeof ggbApplet?.evalCommand !== 'function') return;
    // СНАЧАЛА ТОЧНО, и только если не вышло — числами.
    //
    // Про локус мы знаем больше, чем GeoGebra: у нас есть выражение бегущей
    // точки через букву той, по которой она бежит. Уравнение кривой получается
    // из него исключением параметра — точно, с коэффициентами от букв чертежа
    // и любого порядка. LocusEquation остаётся запасным ходом: она считает
    // численно и печатает четырнадцатизначные целые.
    if (this.#exactLocus(ggbApplet, name)) return;
    // Считаем НЕ СЕЙЧАС.
    //
    // Обработчик зовётся, пока GeoGebra ещё строит локус: спрашивать у неё
    // уравнение в этот момент бесполезно — CAS отвечает «?». Отдаём строку
    // «считаю» и возвращаемся, когда чертёж уляжется.
    this.#row(name, { kind: 'pending', text: 'считаю уравнение локуса…' });
    this.#locusLater(ggbApplet, name, 0);
  }

  // Уравнение локуса ТОЧНО: исключением параметра. Возвращает true, если
  // получилось и строка написана.
  #exactLocus(ggbApplet, name) {
    const parsed = parseCommand(readCommand(ggbApplet, name));
    if (parsed?.name !== 'Locus' || parsed.args.length < 2) return false;
    const [qName, pName] = parsed.args;
    const value = this.pointExpr.get(qName);
    if (!value) return false;                       // бегущая точка нам не выражена
    const letter = this.generators.get(pName)?.letter;
    if (!letter) return false;                      // по чему бежит — неизвестно
    const ti = this.ring.indexOf(letter);
    // У свободной точки сопряжённая независима: параметров два, и «локус»
    // заполняет кусок плоскости, а не кривую. Такое исключать нечем.
    if (ti < 0 || this.#conjIndex(ti) >= 0) return false;
    const zi = this.#locusVarIndex();
    if (zi < 0) return false;

    const cached = this.locusCache.get(name);
    let curve = cached?.value === value ? cached.curve : null;
    if (!curve) {
      curve = implicitize(value, ti, zi, zi + 1);
      this.locusCache.set(name, { value, curve });
    }
    if (!curve) return false;
    const res = this.locus(ggbApplet, curve, this.ring.vars[zi].name, name,
      { draw: false, what: `локус точки ${qName} по ${pName}` });
    return !res.error;
  }

  // Буквы конечны, и кончиться они могут посреди чужого построения. Локус —
  // не тот повод, чтобы валить всю строку: не хватило буквы — спросим GeoGebra.
  #locusVarIndex() {
    if (this.locusVar >= 0) return this.locusVar;
    try {
      const letter = this.#takeLetter();
      this.ring.freePoint(letter);
      this.locusVar = this.ring.indexOf(letter);
    } catch { return -1; }
    return this.locusVar;
  }

  // Спрашиваем уравнение НЕ СРАЗУ и не один раз.
  //
  // LocusEquation считает CAS, а он подгружается лениво и занят, пока GeoGebra
  // достраивает сам локус: первые попытки честно возвращают «ничего». Ждать
  // фиксированную паузу бессмысленно — она либо мала на медленной машине, либо
  // велика на быстрой. Поэтому пробуем несколько раз с растущей задержкой и
  // сдаёмся вслух.
  static LOCUS_TRIES = [150, 500, 1500, 4000];

  #locusLater(ggbApplet, name, attempt) {
    const wait = ComplanatorBridge.LOCUS_TRIES[attempt];
    if (wait === undefined) {
      this.#row(name, { kind: 'unsupported',
        text: 'GeoGebra не смогла выразить этот локус уравнением' });
      return;
    }
    setTimeout(() => {
      try {
        if (!ggbApplet?.exists?.(name)) return;
        const done = this.#locusEquation(ggbApplet, name);
        if (!done) this.#locusLater(ggbApplet, name, attempt + 1);
      } catch { /* чертёж ушёл из-под ног */ }
    }, wait);
  }

  // Возвращает true, если уравнение получено и строка записана.
  #locusEquation(ggbApplet, name) {
    const aux = `${AUX_PREFIX}locus${this.rowNames.size}`;
    let text = null;
    try {
      if (ggbApplet.evalCommand(`${aux}=LocusEquation(${name})`) && ggbApplet.exists(aux)) {
        const got = ggbApplet.getValueString(aux);
        if (got && !got.trim().endsWith('?')) text = got;
      }
    } catch { text = null; }
    try { if (ggbApplet.exists(aux)) ggbApplet.deleteObject(aux); } catch { /* уже нет */ }
    if (!text) return false;
    const world = parseImplicit(text);
    if (!world) {
      // «0 = 0» — это не уравнение, а признание GeoGebra: CAS иногда отвечает
      // так вместо «?». Пробуем ещё раз, а не выводим эту пустоту как ответ.
      const body = text.replace(/^[^:]*:/, '').trim();
      if (/^0\s*=\s*0$/.test(body)) return false;
      this.#row(name, { kind: 'unsupported', text: `уравнение локуса не разобрано: ${body}` });
      return true;
    }
    const ctx = this.#numericContext(ggbApplet);
    if (!ctx) {
      this.#row(name, { kind: 'unsupported', text: 'чертёж не готов: нужны три свободные точки' });
      return true;
    }
    const o = ctx.denorm({ re: 0, im: 0 });
    const local = normPoly(world, o.re, o.im, ctx.radius);
    const order = orderOf(local);
    this.#row(name, {
      kind: order <= 2 ? 'circle' : 'unsupported',
      text: toZBar(local),
      note: `локус, ${order}-й порядок — численно, по LocusEquation`
        + (order <= 2 ? '' : '; строить по нему нельзя'),
    });
    return true;
  }

  // ---- ГМТ ------------------------------------------------------------------
  //
  // Условие на точки и выражение от координат дают равенство нулю. Объявим одну
  // точку бегающей, остальные закреплёнными — и это равенство станет уравнением
  // её геометрического места. Что за кривая вышла, решает СТЕПЕНЬ по этой букве
  // и её сопряжённой: вторая — коника (в частности окружность и прямая), с ней
  // можно работать дальше; третья и выше — кривая, которую мы умеем только
  // нарисовать.

  // Индекс сопряжённой образующей — если она вообще отдельная буква.
  //
  // У свободной точки d и d̄ независимы, и степень надо считать по обеим.
  // У точки на окружности или прямой сопряжение выражается через саму букву,
  // отдельной образующей нет, и всё уже записано одной переменной.
  #conjIndex(i) {
    const rule = this.ring.vars[i]?.conj;
    if (!rule?.num) return -1;
    const terms = rule.num.terms();
    if (terms.length !== 1) return -1;
    const exp = terms[0].exp;
    let found = -1;
    for (let k = 0; k < exp.length; k++) {
      if (!exp[k]) continue;
      if (exp[k] !== 1 || found >= 0) return -1;
      found = k;
    }
    return found;
  }

  // Нарисовать ГМТ по готовому значению. Возвращает описание для панели.
  //
  // Рисуется кривая ЛЮБОГО порядка: пользователь вправе увидеть, что у него
  // получилось. Но работать дальше можно только с коникой — прямой,
  // окружностью, эллипсом, параболой, гиперболой; про остальное так и
  // говорится, и объект помечается как непригодный для построений.
  locus(ggbApplet, value, varName, label, opts = {}) {
    if (!value) return { error: 'нечего рисовать: выражение пусто' };
    // Локус GeoGebra уже нарисован ею самой — второй раз незачем.
    const draw = opts.draw !== false;
    const i = this.ring.indexOf(varName);
    if (i < 0) return { error: `нет такой образующей: ${varName}` };
    const j = this.#conjIndex(i);

    const { degree, coeff } = byPowers(value, i, j);
    if (!degree) return { error: `выражение не зависит от ${varName} — это не ГМТ` };

    const ctx = this.#numericContext(ggbApplet);
    if (!ctx) return { error: 'чертёж не готов: нужны три свободные точки' };
    let flat = null;
    try { flat = realPoly(coeff, r => r.evalFloat(ctx.values)); } catch { flat = null; }
    if (!flat) {
      return { error: 'это равенство задаёт не кривую, а отдельные точки —'
        + ' рисовать нечего' };
    }

    const o = ctx.denorm({ re: 0, im: 0 });
    const world = denormPoly(flat, o.re, o.im, ctx.radius);
    const order = orderOf(world);
    const kind = order <= 2 ? conicKind(fromMap(world)) : `кривая ${order}-го порядка`;
    const usable = order <= 2;
    const name = label ?? this.#freshLocusName(ggbApplet);
    const cmd = `${name}: ${polyCommand(world)}`;
    let drawn = false;
    if (draw) {
      try { drawn = !!ggbApplet?.evalCommand?.(cmd); } catch { drawn = false; }
    }

    // В алгебру точек — с буквой z вместо бегающей: так уравнение читается
    // само по себе, без оглядки на то, как звали точку в условии.
    const asZ = t => String(t).split(varName).join('z');
    this.#row(name, {
      kind: kind === 'прямая' ? 'line' : 'circle',
      text: `${asZ(value.toString())} = 0`,
      tex: `${asZ(value.toTex())} = 0`,
      note: `${opts.what ?? `ГМТ точки ${varName}`}: ${kind}`
        + (usable ? '' : ' — выше второго порядка, строить по ней нельзя')
        + (draw && !drawn ? ' (нарисовать не вышло)' : ''),
    });
    return { name, kind, order, usable, drawn,
             equation: `${asZ(value.toString())} = 0`, command: cmd };
  }
  #freshLocusName(ggbApplet) {
    for (let n = 1; ; n++) {
      const name = `гмт${n}`;
      if (!this.rowNames.has(name) && !(ggbApplet?.exists?.(name))) return name;
    }
  }

  // ---- образующие ---------------------------------------------------------

  #takeLetter() {
    for (const l of EXTRA_LETTERS) {
      if (!this.usedLetters.has(l)) { this.usedLetters.add(l); return l; }
    }
    throw new Error('кончились буквы для образующих');
  }

  // Одна образующая на одно имя объекта: слушатель обновлений срабатывает и на
  // перетаскивании, а заводить при этом новую переменную нельзя.
  #generator(name, make) {
    let g = this.generators.get(name);
    if (!g) {
      g = make();
      this.generators.set(name, g);
      // Запоминаем, из какого объекта чертежа взялась каждая переменная кольца:
      // без этого нечем подставлять настоящие координаты при сверке.
      const i = this.ring.indexOf(g.letter);
      this.varSource[i] = { obj: name, conj: false };
      if (this.ring.vars[i + 1]?.kind === 'conj') {
        this.varSource[i + 1] = { obj: name, conj: true };
      }
      if (g.unit) this.unitObjects.push(name);
    }
    this.pointExpr.set(name, g.expr);
    return g;
  }

  // ---- командная строка ---------------------------------------------------

  // Каждая строка — отдельная система. Ошибка в одной не мешает остальным.
  // Бюджет на счёт нужен КАЖДОМУ входу, а не только обработке объектов чертежа.
  //
  // Этого не хватало дольше всего: строка «не посчитано» работала для построений
  // мышью, а командная строка считала без всякого ограничения и вешала вкладку
  // молча. Причём именно туда пользователь и уходит, когда мышью не выходит —
  // то есть ограничение отсутствовало ровно там, где оно нужнее всего.
  runCommands(ggbApplet, text, budgetMs = ComplanatorBridge.COMPUTE_BUDGET_MS) {
    const report = [];
    for (const line of parseProgram(text)) {
      if (line.error) { report.push({ line: line.index + 1, source: line.source, error: line.error }); continue; }
      try {
        const created = withFactorBudget(() => withComputeBudget(budgetMs,
          () => this.#solveLine(ggbApplet, line)));
        report.push({ line: line.index + 1, source: line.source, created });
      } catch (e) {
        report.push(e instanceof BudgetExceeded
          ? {
            line: line.index + 1,
            source: line.source,
            error: `не посчитано за ${(e.budgetMs / 1000).toFixed(0)} с`,
            estimate: estimateWait(e.peak),
            compute: () => this.runCommands(ggbApplet, line.source, ComplanatorBridge.EXTENDED_BUDGET_MS),
          }
          : { line: line.index + 1, source: line.source, error: e.message });
      }
    }
    return report;
  }

  // Прямые и окружности панели — под своими именами. Нужны и строке выражений
  // (distance(P, f)), и построениям (radline(k, P)).
  #objectEnv() {
    const objects = new Map();
    for (const [name, def] of this.lineDefs) objects.set(name, { kind: 'line', eq: def.eq });
    for (const [name, eq] of this.circleDefs) objects.set(name, { kind: 'circle', eq });
    for (const [name, eq] of this.conicDefs) objects.set(name, { kind: 'conic', eq });
    return objects;
  }

  #mainContext() {
    return { vars: this.pointExpr, objects: this.#objectEnv(), ring: this.ring };
  }

  #solveLine(ggbApplet, line) {
    // Построения ничего не утверждают про точку — их не решают, а исполняют.
    // Разбор уже проверил, что в строке они не смешаны с условиями.
    if (kindOf(line.commands[0]) === 'build') return this.#runBuilds(ggbApplet, line);

    // Неизвестными заново считаем только те свои точки, которые задала ЭТА ЖЕ
    // строка: тогда её повторный запуск пересчитывает, а следующие строки
    // спокойно ссылаются на построенное раньше.
    const mine = line.source.trim();
    const knownNames = new Set([...this.pointExpr.keys()]
      .filter(n => this.commandPoints.get(n)?.source !== mine));

    const solved = solveSystem(line.commands, knownNames);

    // Подставляем: известные точки — своими выражениями в главном кольце,
    // и заодно их сопряжения (в локальном кольце это отдельные образующие).
    const values = [];
    for (const name of solved.known) {
      const index = solved.local.indexOf(`«${name}»`);
      const expr = this.pointExpr.get(name);
      values[index] = expr;
      values[index + 1] = expr.conjugate();
    }

    const created = [];
    let placed = false;

    // ОТВЕТ ИРРАЦИОНАЛЕН — ЭТО НЕ ОТКАЗ.
    //
    // Система вернула рецепт «корень уравнения x² − Sx + Q = 0»: сама она в
    // локальном кольце, а расширение надо заводить там, где живут настоящие
    // выражения вершин. Подставляем S и Q — и присоединяем корень, ровно так
    // же, как это делается для пересечения прямой с окружностью.
    //
    // Точек получается ДВЕ, и выбрать между ними нечем: условие выполняется на
    // обеих. Поэтому выдаются обе, как у команды meet.
    if (solved.pending) {
      const { name, S, Q } = solved.pending;
      const got = adjoinBySumAndProduct(S.substituteInto(values), Q.substituteInto(values),
        `t${this.extCount + 1}`);
      if (got.kind === 'extended') this.extCount++;
      got.roots.forEach((expr, index) => {
        const label = got.roots.length > 1 ? `${name}${index + 1}` : name;
        this.commandPoints.set(label, { expr, source: line.source.trim() });
        this.pointExpr.set(label, expr);
        created.push({ name: label, text: expr.toString(), tex: expr.toTex() });
        placed = this.#placePoint(ggbApplet, label, expr) || placed;
        this.#row(label, {
          kind: 'point',
          text: expr.toString(),
          tex: expr.toTex(),
          note: `из командной строки: ${line.source.trim()}`
            + (got.kind === 'extended' ? ' (корень присоединён)' : ''),
          check: this.#verify(this.#numericContext(ggbApplet), ggbApplet, label, expr),
        });
      });
      return created;
    }

    for (const [name, answer] of solved.answers) {
      const expr = answer.substituteInto(values);
      this.commandPoints.set(name, { expr, source: line.source.trim() });
      this.pointExpr.set(name, expr);
      created.push({ name, text: expr.toString(), tex: expr.toTex() });
      placed = this.#placePoint(ggbApplet, name, expr) || placed;
      this.#row(name, {
        kind: 'point',
        text: expr.toString(),
        tex: expr.toTex(),
        note: `из командной строки: ${line.source.trim()}`,
        check: this.#verify(this.#numericContext(ggbApplet), ggbApplet, name, expr),
      });
    }
    return created;
  }

  // ---- построения из командной строки --------------------------------------

  #runBuilds(ggbApplet, line) {
    const ctx = this.#mainContext();
    const created = [];
    line.commands.forEach((command, index) => {
      const key = `${line.source.trim()}#${index}`;
      // Команда вправе создать не один объект: у гомотетии центров два, у
      // касательной из внешней точки — две прямые.
      const made = this.#runBuild(ggbApplet, command, key, ctx);
      for (const item of (Array.isArray(made) ? made : [made])) created.push(item);
    });
    return created;
  }

  #runBuild(ggbApplet, command, key, ctx) {
    switch (command.name) {
      case 'buildpoint': return this.#buildPoint(ggbApplet, command, key, ctx);
      case 'homothety': return this.#buildHomothetyCenters(ggbApplet, command, key, ctx);
      case 'tangent': return this.#buildTangents(ggbApplet, command, key, ctx);
      case 'commontangent': return this.#buildCommonTangents(ggbApplet, command, key, ctx);
      case 'conic5': case 'parabola': case 'conic':
        return this.#buildConic(ggbApplet, command, key, ctx);
      case 'centre': return this.#buildConicCentre(ggbApplet, command, key);
      case 'polar': return this.#buildPolar(ggbApplet, command, key, ctx);
      case 'meet': return this.#buildMeet(ggbApplet, command, key);
      case 'compass': return this.#buildCompass(ggbApplet, command, key, ctx);
      case 'isogonal': case 'rot90': case 'rot60': case 'krokhalyator':
        return this.#buildNamedPoint(ggbApplet, command, key, ctx);
      case 'incenter': return this.#buildIncenter(ggbApplet, command, key);
      case 'semiincircle': return this.#buildSemiincircle(ggbApplet, command, key);
      case 'segcircle': return this.#buildSegmentCircles(ggbApplet, command, key, ctx);
      default: return this.#buildLineObject(ggbApplet, command, key, ctx);
    }
  }

  // Имя для построенного объекта. Без явного имени оно выдаётся один раз на
  // текст строки: иначе повторный запуск той же команды рисовал бы вторую точку
  // поверх первой, и так до бесконечности.
  #freshLabel(ggbApplet, command, key, prefix) {
    if (command.label) return command.label;
    return this.#pickName(ggbApplet, key, prefix);
  }

  // Свободное имя под построенный объект. Помним его по ключу: повторный заход
  // (обновление чертежа, повторный запуск команды) обязан вернуть ТО ЖЕ имя, а
  // не завести копию.
  #pickName(ggbApplet, key, prefix) {
    const remembered = this.buildNames.get(key);
    if (remembered) return remembered;
    const taken = name => this.rowNames.has(name) || this.pointExpr.has(name)
      || this.lineDefs.has(name) || this.circleDefs.has(name)
      || (typeof ggbApplet?.exists === 'function' && ggbApplet.exists(name));
    for (let n = 1; n < 1000; n++) {
      const candidate = `${prefix}${n}`;
      if (taken(candidate)) continue;
      this.buildNames.set(key, candidate);
      return candidate;
    }
    throw new Error('не удалось подобрать имя для построенного объекта');
  }

  // buildpoint(выражение) — точка прямо по формуле, без всяких условий.
  //
  // Выражение не обязано быть однородным первой степени: a^2 и 1/a — законные
  // точки. Смысл им придаёт то, что нормировка чертежа (z ↦ (z−O)/R) НЕ
  // содержит поворота, то есть комплексная единица — вполне определённая точка
  // описанной окружности, и buildpoint(1) её рисует.
  #buildPoint(ggbApplet, command, key, ctx) {
    const expr = evalAst(command.args[0], ctx);
    const name = this.#freshLabel(ggbApplet, command, key, 'K');
    this.commandPoints.set(name, { expr, source: command.source });
    this.pointExpr.set(name, expr);
    this.#placePoint(ggbApplet, name, expr);
    this.#row(name, {
      kind: 'point',
      text: expr.toString(),
      tex: expr.toTex(),
      note: `из командной строки: ${command.source}`,
      check: this.#verify(this.#numericContext(ggbApplet), ggbApplet, name, expr),
    });
    return { name, text: expr.toString(), tex: expr.toTex() };
  }

  // Готовые построения планиметрии: та же точка, что и через buildpoint, но
  // формулу за пользователя выводит движок.
  //
  // Всё здесь рационально в a, b, c — и потому считается точно, без радикалов.
  // Инцентр к этой компании не относится: он от них не выражается вовсе.
  #namedPointExpr(command, ctx) {
    const arg = i => evalAst(command.args[i], ctx);
    switch (command.name) {
      // Поворот вокруг центра; без центра — вокруг центра описанной, а он у
      // движка ровно ноль (нормировка чертежа делает описанную единичной).
      case 'rot90': {
        const z = arg(0);
        const o = command.args.length > 1 ? arg(1) : this.ring.zero();
        return F.rotateQuarter(z, 1, o);
      }
      // Поворот на 60°: умножение на первообразный корень шестой степени.
      // unity(6) уже есть в языке выражений, здесь он же, но своим именем.
      case 'rot60': {
        const z = arg(0);
        const o = command.args.length > 1 ? arg(1) : this.ring.zero();
        return o.add(z.sub(o).mul(rootOfUnity(this.ring, 6)));
      }
      // Ортоцентр трёх точек — та самая четвёртая точка ортоцентрической
      // четвёрки: H = P + Q + R − 2·O, где O — центр описанной около PQR.
      case 'krokhalyator': return F.orthocenter(arg(0), arg(1), arg(2));
      case 'isogonal': {
        const got = F.isogonal(arg(0), this.#triangle());
        if (!got) throw new Error('изогональное сопряжение: точка лежит на стороне треугольника');
        return got;
      }
      default: throw new Error(`неизвестное построение ${command.name}`);
    }
  }

  // Вершины треугольника — первые три свободные точки чертежа. Именно они и
  // есть буквы a, b, c, относительно которых считает весь движок.
  #triangle() {
    const names = this.freeOrder.slice(0, 3);
    if (names.length < 3) throw new Error('нужен треугольник: поставьте три свободные точки');
    return names.map(n => this.pointExpr.get(n));
  }

  // Инцентр.
  //
  // Через a, b, c он НЕ выражается: это единственный из главных центров,
  // которому нужны длины сторон, а они иррациональны. Зато выражается через
  // середины дуг: инцентр — ортоцентр треугольника середин дуг, а они лежат на
  // описанной, поэтому I = M_A + M_B + M_C.
  //
  // Середина дуги — квадратный корень: M_A² = bc. Присоединяем ДВА корня, а не
  // три: из M_A·M_B = −c·M_C третья середина выражается через первые две, и
  // лишнее расширение только раздуло бы выражение.
  //
  // Какой из двух корней «наш» — вопрос не алгебры, а чертежа: √(bc) даёт обе
  // середины дуги BC, и не та даёт эксцентр вместо инцентра. Поэтому корень не
  // вычисляется, а СТРОИТСЯ: GeoGebra пересекает серединный перпендикуляр к BC
  // с описанной, и берётся точка дальше от A — середина дуги, не содержащей A.
  #buildIncenter(ggbApplet, command, key) {
    const names = this.#ensureComplexFrame(ggbApplet);
    if (!names) throw new Error('нужен треугольник: поставьте три свободные точки');
    const [ga, gb, gc] = this.unitObjects;
    const [a, b, c] = this.#triangle();

    const circ = new CircleEq(this.ring.zero(), this.ring.one());
    // Имя берётся и точка рисуется В ОДИН ЗАХОД.
    //
    // Разнести это нельзя: свободное имя ищется в том числе по чертежу, и пока
    // первая середина дуги не построена, второй запрос отвечает тем же именем.
    // Так и вышло — обе дуги назвались M1, вторая не построилась вовсе, и
    // вместо инцентра получался эксцентр.
    const arc = (suffix, near, far1, far2, q) => {
      const label = this.#pickName(ggbApplet, `${key}#${suffix}`, 'M');
      const ext = new QuadraticExt(this.ring, this.ring.zero(), q.neg(), label).setCircleRule(circ);
      this.#drawArcMidpoint(ggbApplet, label, near, far1, far2);
      ext.ggbRoot = `((ToComplex(${label}) - ToComplex(${AUX_PREFIX}O)) / ${AUX_PREFIX}R)`;
      ext.ggbName = label;
      ext.name = label;
      this.extensions.push(ext);
      return { root: ext.root(), label };
    };

    const arcA = arc('MA', ga, gb, gc, b.mul(c));
    const arcB = arc('MB', gb, gc, ga, c.mul(a));
    const MA = arcA.root, MB = arcB.root;
    const expr = MA.add(MB).sub(MA.mul(MB).div(c));
    // Середина дуги остаётся при инцентре: полувписанная окружность считается
    // над ней, и пересчитывать её значило бы завести ВТОРОЙ корень из того же
    // bc — лишнее расширение на ровном месте.
    this.incenterParts = { I: expr, MA, A: a, labels: [arcA.label, arcB.label] };

    const name = command.label ?? this.#pickName(ggbApplet, key, 'I');
    this.commandPoints.set(name, { expr, source: command.source });
    this.pointExpr.set(name, expr);
    this.#placePoint(ggbApplet, name, expr);
    this.#row(name, {
      kind: 'point',
      text: expr.toString(),
      tex: expr.toTex(),
      note: `инцентр через середины дуг ${arcA.label}, ${arcB.label}`,
      check: this.#verify(this.#numericContext(ggbApplet), ggbApplet, name, expr),
    });
    return { name, text: expr.toString(), tex: expr.toTex() };
  }

  // ПОЛУВПИСАННАЯ ОКРУЖНОСТЬ в угле A: касается AB, AC и описанной изнутри.
  //
  // Строится поверх инцентра, и это не экономия, а необходимость: середины дуг
  // уже присоединены ради него, а над ними всё остальное РАЦИОНАЛЬНО (см.
  // F.semiincircle). Посчитать её «с нуля» значило бы извлечь тот же корень
  // второй раз и получить расширение расширения — ответ вырос бы на порядок, а
  // сравнения перестали бы сходиться.
  //
  // Рисуется через точку касания: Circle(центр, T). Так в чертёж не попадает ни
  // одного радикала — GeoGebra строит окружность по центру и точке на ней.
  #buildSemiincircle(ggbApplet, command, key) {
    if (!this.incenterParts) {
      // Инцентр строим сами, если его ещё не просили: иначе команда требовала
      // бы от пользователя помнить порядок строк.
      this.#buildIncenter(ggbApplet, { ...command, label: null, source: command.source },
        `${key}#I`);
    }
    const parts = this.incenterParts;
    if (!parts) throw new Error('полувписанная строится от инцентра: нужен треугольник');
    const got = F.semiincircle(parts.A.mul(parts.A), parts.I, parts.MA);
    const eq = new CircleEq(got.centre, got.r2);
    const name = this.#freshLabel(ggbApplet, command, key, 'k');
    this.circleDefs.set(name, eq);
    const tName = this.#pickName(ggbApplet, `${key}#T`, 'T');
    this.commandPoints.set(tName, { expr: got.touch, source: command.source });
    this.pointExpr.set(tName, got.touch);
    this.#placePoint(ggbApplet, tName, got.touch);
    this.#row(tName, {
      kind: 'point', text: got.touch.toString(), tex: got.touch.toTex(),
      note: `точка касания полувписанной с описанной`,
    });
    this.#row(name, {
      kind: 'circle', text: eq.toString(), tex: eq.toTex(),
      canonical: () => eq.toCanonical(),
      note: `полувписанная окружность в угле A (касается в ${tName})`,
    });
    return { name, text: eq.toString(), tex: eq.toTex() };
  }

  // ОКРУЖНОСТИ, ВПИСАННЫЕ В СЕГМЕНТ: касаются хорды BC и описанной в точке P.
  //
  // Их ДВЕ — по одной в каждый из двух сегментов, на которые хорда делит круг,
  // и обе законны. Какая нужна, решает тот, кто смотрит на чертёж, поэтому
  // выдаются обе: угадывать за пользователя тут нельзя, а спутать их легче
  // всего (см. formulas.js и test/segment-circle.test.js).
  //
  // Корень присоединяется ТОТ ЖЕ, что у инцентра: m² = bc, то есть середина
  // дуги BC. Нового радикала не возникает, и это главное — иначе ответ вырос бы
  // на порядок, а сравнения перестали бы сходиться.
  #buildSegmentCircles(ggbApplet, command, key, ctx) {
    const [p, b, c] = command.args.map(ast => evalAst(ast, ctx));
    const circ = new CircleEq(this.ring.zero(), this.ring.one());
    const label = this.#pickName(ggbApplet, `${key}#m`, 'M');
    const ext = new QuadraticExt(this.ring, this.ring.zero(), b.mul(c).neg(), label)
      .setCircleRule(circ);
    this.extensions.push(ext);
    const both = F.segmentCircle(p, b, c, ext.root());
    const made = [];
    both.forEach((g, index) => {
      const eq = new CircleEq(g.centre, g.r2);
      const name = this.#pickName(ggbApplet, `${key}#${index}`, 'k');
      this.circleDefs.set(name, eq);
      this.#row(name, {
        kind: 'circle', text: eq.toString(), tex: eq.toTex(),
        canonical: () => eq.toCanonical(),
        note: `окружность в сегменте, касается дуги в ${command.args[0].name ?? 'P'}`
          + ` (ветвь ${index + 1} из 2)`,
      });
      made.push({ name, text: eq.toString(), tex: eq.toTex() });
    });
    return made;
  }

  // Середина дуги XY, не содержащей Z: пересечение серединного перпендикуляра к
  // XY с описанной, из двух точек — дальняя от Z.
  #drawArcMidpoint(ggbApplet, label, Z, X, Y) {
    if (typeof ggbApplet?.evalCommand !== 'function') {
      throw new Error('инцентр строится по чертежу: нужен работающий апплет');
    }
    if (ggbApplet.exists(label)) return;
    const circle = `${AUX_PREFIX}Circ`;
    if (!this.auxObjects.has(circle)) {
      const [A, B, C] = this.unitObjects;
      if (!ggbApplet.evalCommand(`${circle}=Circle(${A},${B},${C})`)) {
        throw new Error('GeoGebra не приняла описанную окружность');
      }
      this.auxObjects.add(circle);
      ggbApplet.evalCommand(`SetVisibleInView(${circle},1,false)`);
    }
    const bis = `${AUX_PREFIX}Bis${label}`;
    if (!ggbApplet.evalCommand(`${bis}=PerpendicularBisector(${X},${Y})`)) {
      throw new Error(`GeoGebra не приняла серединный перпендикуляр к ${X}${Y}`);
    }
    this.auxObjects.add(bis);
    ggbApplet.evalCommand(`SetVisibleInView(${bis},1,false)`);
    // По одной точке на индекс: Intersect(окружность, прямая) списка не
    // возвращает, и Element по нему не берётся — на этом команда и падала.
    const one = `${AUX_PREFIX}Arc1${label}`, two = `${AUX_PREFIX}Arc2${label}`;
    for (const [nm, idx] of [[one, 1], [two, 2]]) {
      if (!ggbApplet.evalCommand(`${nm}=Intersect(${circle},${bis},${idx})`)) {
        throw new Error('GeoGebra не смогла пересечь серединный перпендикуляр с описанной');
      }
      this.auxObjects.add(nm);
      ggbApplet.evalCommand(`SetVisibleInView(${nm},1,false)`);
    }
    const ok = ggbApplet.evalCommand(
      `${label}=If(Distance(${Z},${one})>Distance(${Z},${two}),${one},${two})`);
    if (!ok) throw new Error(`GeoGebra не смогла выбрать середину дуги ${label}`);
  }

  #buildNamedPoint(ggbApplet, command, key, ctx) {
    const expr = this.#namedPointExpr(command, ctx);
    const prefix = { isogonal: 'P', rot90: 'R', rot60: 'R', krokhalyator: 'H' }[command.name] ?? 'K';
    const name = this.#freshLabel(ggbApplet, command, key, prefix);
    this.commandPoints.set(name, { expr, source: command.source });
    this.pointExpr.set(name, expr);
    this.#placePoint(ggbApplet, name, expr);
    this.#row(name, {
      kind: 'point',
      text: expr.toString(),
      tex: expr.toTex(),
      note: `из командной строки: ${command.source}`,
      check: this.#verify(this.#numericContext(ggbApplet), ggbApplet, name, expr),
    });
    return { name, text: expr.toString(), tex: expr.toTex() };
  }

  // buildline(A, B, C) — прямая по уравнению A·z + B·z̄ + C = 0;
  // radline(объект, объект) — их радикальная ось (точка = окружность нулевого
  // радиуса, поэтому «ось» двух точек — это срединный перпендикуляр).
  // compass(A, B, C) — циркуль: раствор AB, ножка в C.
  //
  // Единственная тонкость на стороне GeoGebra: нарисовать окружность по центру
  // и КВАДРАТУ радиуса нельзя, а сам радиус иррационален и выражением движка не
  // является. Поэтому длину считает сама GeoGebra — `Distance` по двум точкам,
  // построенным из наших выражений. Символьная часть при этом остаётся точной:
  // в панели стоит r², а приближение живёт только на чертеже.
  #buildCompass(ggbApplet, command, key, ctx) {
    const [from, to, center] = command.args.map(ast => evalAst(ast, ctx));
    const eq = CircleEq.compass(from, to, center);
    const name = this.#freshLabel(ggbApplet, command, key, 'k');
    this.circleDefs.set(name, eq);
    this.#placeCompass(ggbApplet, name, from, to, center);
    this.#row(name, {
      kind: 'circle',
      text: eq.toString(),
      tex: eq.toTex(),
      canonical: () => eq.toCanonical(),
      note: `построено: ${command.source}`,
    });
    return { name, text: eq.toString(), tex: eq.toTex() };
  }

  #placeCompass(ggbApplet, name, from, to, center) {
    if (!this.drawing) return false;
    const names = this.#ensureComplexFrame(ggbApplet);
    if (!names) return false;
    if (![from, to, center].every(isDrawableValue)) return false;
    const at = expr => `ToPoint(ToComplex(${AUX_PREFIX}O) + ${AUX_PREFIX}R*${valueToGgb(expr, names)})`;
    const ok = ggbApplet.evalCommand(
      `${name}=Circle(${at(center)},Distance(${at(from)},${at(to)}))`);
    if (!ok) throw new Error('GeoGebra не приняла определение окружности циркуля');
    return true;
  }

  #buildLineObject(ggbApplet, command, key, ctx) {
    const eq = command.name === 'radline'
      ? CircleEq.radicalAxis(this.#asCircle(command.args[0], ctx), this.#asCircle(command.args[1], ctx))
      : this.#lineFromCoefficients(command.args.map(ast => evalAst(ast, ctx)));
    const name = this.#freshLabel(ggbApplet, command, key, 'l');
    this.commandLines.set(name, { eq, source: command.source });
    this.lineDefs.set(name, { p: null, q: null, eq });
    this.#placeLine(ggbApplet, name, eq);
    this.#row(name, {
      kind: 'line',
      text: eq.toString(),
      tex: eq.toTex(),
      canonical: () => eq.toCanonical(),
      note: `построено: ${command.source}`,
    });
    return { name, text: eq.toString(), tex: eq.toTex() };
  }

  // homothety(k1, k2) — центры гомотетии двух окружностей.
  //
  // Центры делят отрезок между центрами в отношении ±r₁:r₂, то есть
  // P± = (r₁o₂ ∓ r₂o₁)/(r₁ ∓ r₂). Радиусов у движка нет — он хранит квадраты,
  // потому что сам радиус иррационален. Но избавиться от них можно: домножив
  // числитель и знаменатель на сопряжённое, получаем
  //
  //     P± = [ (r₁²o₂ − r₂²o₁) ± t·(o₂ − o₁) ] / (r₁² − r₂²),   t = r₁·r₂,
  //
  // и единственный корень здесь — t = √(r₁²·r₂²). Это заметно слабее, чем знать
  // оба радиуса: при r₁² = 2 и r₂² = 8 произведение t = 4 рационально, хотя
  // ни один радиус таковым не является.
  //
  // Знак корня символьно не определён, поэтому какая из двух точек внешняя, а
  // какая внутренняя, решает чертёж, а не формула: обе строятся сразу.
  // Центры гомотетии как ВЫРАЖЕНИЯ, без рисования: они нужны не только команде
  // homothety, но и общим касательным — те через них и проходят.
  #homothetyCenters(k1, k2) {
    const diff = k1.r2.sub(k2.r2);
    // Равные радиусы: внешний центр уходит в бесконечность, внутренний остаётся
    // серединой между центрами — и это осмысленный ответ, а не ошибка.
    if (diff.isZero()) {
      return [{ expr: k1.center.add(k2.center).div(2n),
                note: 'внутренний центр гомотетии; радиусы равны, внешний — на бесконечности' }];
    }
    const t = k1.r2.mul(k2.r2).sqrt();
    if (!t) return null;                  // произведение радиусов иррационально
    const base = k2.center.mul(k1.r2).sub(k1.center.mul(k2.r2));
    const shift = k2.center.sub(k1.center).mul(t);
    return [
      { expr: base.add(shift).div(diff), note: 'центр гомотетии двух окружностей' },
      { expr: base.sub(shift).div(diff),
        note: 'второй центр гомотетии (внешний и внутренний различает чертёж)' },
    ];
  }

  #buildHomothetyCenters(ggbApplet, command, key, ctx) {
    const k1 = this.#namedCircle(command.args[0], 'homothety');
    const k2 = this.#namedCircle(command.args[1], 'homothety');
    const centers = this.#homothetyCenters(k1, k2);
    if (!centers) {
      throw new Error('homothety: произведение радиусов иррационально — '
        + 'такой центр через a, b, c не выражается');
    }
    return centers.map((c, i) =>
      this.#emitPoint(ggbApplet, command, `${key}#${i + 1}`, c.expr, c.note));
  }

  // commontangent(k1, k2) — общие касательные двух окружностей.
  //
  // Отдельной механики не нужно: общая касательная проходит через центр
  // гомотетии (внешние — через внешний, внутренние — через внутренний), а
  // касательные из точки движок уже строит. Поэтому команда складывается из
  // двух готовых, и заодно ставит на чертёж сами центры — через них всё и
  // объясняется.
  //
  // Пар может оказаться меньше четырёх, и это не сбой: у пересекающихся
  // окружностей внутренних касательных нет вовсе, у касающихся они сливаются в
  // одну. Поэтому неудача одного центра не отменяет второй.
  #buildCommonTangents(ggbApplet, command, key, ctx) {
    const k1 = this.#namedCircle(command.args[0], 'commontangent');
    const k2 = this.#namedCircle(command.args[1], 'commontangent');
    const circleName = command.args[0]?.t === 'name' ? command.args[0].name : null;
    const centers = this.#homothetyCenters(k1, k2);
    if (!centers) {
      throw new Error('commontangent: произведение радиусов иррационально — '
        + 'центр гомотетии через a, b, c не выражается');
    }
    // Объектов получается много, и общее имя им не годится: под ним оказались
    // бы все сразу.
    const anon = { ...command, label: null };
    const created = [];
    const problems = [];
    centers.forEach((c, i) => {
      const centre = this.#emitPoint(ggbApplet, anon, `${key}#c${i}`, c.expr, c.note);
      created.push(centre);
      try {
        created.push(...this.#tangentsFrom(ggbApplet, anon, `${key}#t${i}`, c.expr, k1,
          circleName, centre.name, 'общая касательная двух окружностей'));
      } catch (e) {
        problems.push(e.message);
      }
    });
    if (!created.some(o => o.kind !== 'point') && problems.length) {
      throw new Error(`commontangent: ${problems.join('; ')}`);
    }
    return created;
  }

  // tangent(P, k) — касательные из точки P к окружности k.
  //
  // Точки касания — это пересечение ПОЛЯРЫ точки P с самой окружностью: поляра
  // точки, лежащей на окружности, и есть касательная в ней. А касательная в
  // найденной точке касания T — снова поляра, только уже точки T. Никакой
  // отдельной механики не нужно, всё выражается через уже готовое.
  //
  // Если P лежит на окружности, поляра её касается, корень двойной — и
  // касательная получается ровно одна, что и правильно.
  #buildTangents(ggbApplet, command, key, ctx) {
    const p = evalAst(command.args[0], ctx);
    const circleName = command.args[1]?.name;
    const k = this.#namedCircle(command.args[1], 'tangent');
    const polarOf = command.args[0]?.t === 'name' ? command.args[0].name : null;
    return this.#tangentsFrom(ggbApplet, command, key, p, k, circleName, polarOf,
      'касательная из точки к окружности');
  }

  // Касательные из точки p к окружности k. Вынесено из #buildTangents, потому
  // что ровно это же нужно общим касательным двух окружностей — только точкой
  // там служит центр гомотетии.
  #tangentsFrom(ggbApplet, command, key, p, k, circleName, polarOf, what) {
    const polar = k.polarLine(p);
    // Точки касания из произвольной внешней точки иррациональны — раньше здесь
    // была капитуляция. Теперь корень присоединяется к полю, и касательные
    // выражаются через него (см. quadratic-ext.js).
    const solved = lineMeetsCircleExtended(polar, k, this.#knownPoints(), 't');
    if (solved.roots.length === 0) {
      throw new Error(QUADRATIC_EXCUSE[solved.kind]
        ?? 'точки касания через a, b, c не выражаются');
    }
    const single = solved.roots.length === 1;
    const created = [];

    // Сначала САМИ ТОЧКИ КАСАНИЯ — спрашивают обычно именно их, а не только
    // прямые. Если корень иррационален, первая точка его и определяет: она
    // строится пересечением, и через неё выражается всё остальное.
    solved.roots.forEach((touch, index) => {
      const label = this.#freshLabel(ggbApplet, command, `${key}#p${index}`, 'T');
      if (solved.ext && index === 0 && this.drawing) {
        // Если внешняя точка названа на чертеже, секущая строится родной
        // командой Polar — короткой и быстрой.
        this.#realizeRoot(ggbApplet, solved.ext, polar, circleName, label, polarOf);
        this.commandPoints.set(label, { expr: touch, source: command.source });
        this.pointExpr.set(label, touch);
        this.#row(label, {
          kind: 'point',
          text: touch.toString(),
          tex: touch.toTex(),
          note: `точка касания: ${command.source}`,
        });
        created.push({ name: label, text: touch.toString(), tex: touch.toTex() });
        return;
      }
      created.push(this.#emitPoint(ggbApplet, command, `${key}#p${index}`, touch,
        single ? 'точка касания (точка лежит на окружности)' : 'точка касания'));
    });

    // И только потом касательные.
    //
    // Отдаём их GeoGebra её же РОДНОЙ командой Tangent(T, k), а не своей парой
    // ToPoint(...) с развёрнутым выражением. Это оказалось решающим: наши
    // определения разворачиваются до вершин a, b, c, поэтому прямая через точку
    // на касательной весила под шесть тысяч знаков — и GeoGebra вставала,
    // пересчитывая эту простыню на каждое обновление чертежа, ещё до того как
    // наш код получал управление. Наш бюджет туда не дотягивается: там считает
    // не наш код. А Tangent(T_1, k) — три десятка знаков и родной алгоритм.
    //
    // Уравнение при этом остаётся нашим: в таблицу идёт то, что посчитал
    // движок, а GeoGebra отвечает только за картинку.
    solved.roots.forEach((touch, index) => {
      const touchName = created[index]?.name;
      const native = touchName && circleName ? `Tangent(${touchName},${circleName})` : null;
      created.push(this.#emitLine(ggbApplet, command, `${key}#l${index}`, k.polarLine(touch),
        single ? `${what}: точка лежит на окружности` : what, native));
    });
    return created;
  }

  // Коника: три способа задать и один объект на выходе.
  //
  // Рисует её сама GeoGebra родными командами — Conic по пяти точкам, Parabola
  // по фокусу и директрисе, Ellipse/Hyperbola по фокусам и точке. Уравнение при
  // этом остаётся нашим: в панель идёт то, что посчитал движок, а GeoGebra
  // отвечает только за картинку. Иначе пришлось бы разворачивать шесть
  // коэффициентов в её систему координат — длинно и незачем.
  #buildConic(ggbApplet, command, key, ctx) {
    const name = this.#freshLabel(ggbApplet, command, key, 'q');
    let eq, native;
    if (command.name === 'conic5') {
      const pts = command.args.map(ast => evalAst(ast, ctx));
      eq = ConicEq.throughFivePoints(pts);
      if (!eq) throw new Error('conic5: через эти пять точек коника не определяется');
      native = this.#nativeFromNames(command.args, 'Conic');
    } else if (command.name === 'parabola') {
      const focus = evalAst(command.args[0], ctx);
      const line = this.#namedLine(command.args[1], 'parabola');
      eq = ConicEq.parabola(focus, line);
      native = this.#nativeFromNames(command.args, 'Parabola');
    } else {
      const [f1, f2, through] = command.args.map(ast => evalAst(ast, ctx));
      const a2 = ConicEq.squaredAxis(f1, f2, through);
      if (!a2) {
        throw new Error('conic: полуось через a, b, c не выражается — '
          + 'произведение расстояний до фокусов иррационально');
      }
      eq = ConicEq.byFociAndSquaredAxis(f1, f2, a2.value);
      native = this.#nativeFromNames(command.args, a2.hyperbola ? 'Hyperbola' : 'Ellipse');
    }

    this.conicDefs.set(name, eq);
    if (native && this.drawing) ggbApplet?.evalCommand(`${name}=${native}`);
    this.#row(name, {
      kind: 'conic',
      text: eq.toString(),
      tex: eq.toTex(),
      note: `построено: ${command.source}`,
    });
    return { name, text: eq.toString() };
  }

  // Родная команда GeoGebra строится только когда ВСЕ аргументы названы на
  // чертеже: подставлять развёрнутые выражения бессмысленно — они разрастаются
  // до тысяч знаков, и GeoGebra встаёт на собственном пересчёте.
  #nativeFromNames(args, command) {
    const names = args.map(a => (a.t === 'name' ? a.name : null));
    if (names.some(n => !n)) return null;
    return `${command}(${names.join(',')})`;
  }

  #buildConicCentre(ggbApplet, command, key) {
    const q = this.#namedConic(command.args[0], 'centre');
    const centre = q.centre();
    if (!centre) throw new Error('centre: у этой коники центра нет (это парабола)');
    return this.#emitPoint(ggbApplet, command, key, centre, 'центр коники');
  }

  // Поляра точки — и относительно коники, и относительно окружности: у
  // окружности это частный случай, отдельной команды он не заслуживает.
  //
  // Поляра точки, лежащей на кривой, — касательная в ней; никакой особой ветки
  // для этого не нужно, формула одна и та же.
  #buildPolar(ggbApplet, command, key, ctx) {
    const p = evalAst(command.args[0], ctx);
    const target = command.args[1];
    const conic = target.t === 'name' ? this.conicDefs.get(target.name) : null;
    const circle = target.t === 'name' ? this.circleDefs.get(target.name) : null;
    if (!conic && !circle) {
      throw new Error(`polar: «${target.t === 'name' ? target.name : '…'}» — `
        + 'не коника и не окружность с панели');
    }
    const eq = conic ? conic.polar(p) : circle.polarLine(p);
    if (!eq) throw new Error('polar: поляра вырождена — точка в центре коники');
    const native = command.args[0].t === 'name'
      ? `Polar(${command.args[0].name},${target.name})` : null;
    return this.#emitLine(ggbApplet, command, key, eq,
      conic ? 'поляра относительно коники' : 'поляра относительно окружности', native);
  }

  #namedConic(ast, who) {
    if (ast.t === 'name') {
      const q = this.conicDefs.get(ast.name);
      if (q) return q;
      throw new Error(`${who}: «${ast.name}» — не коника с панели`);
    }
    throw new Error(`${who}: нужна коника, заданная буквой с панели`);
  }

  #namedLine(ast, who) {
    if (ast.t === 'name') {
      const l = this.lineDefs.get(ast.name);
      if (l) return l.eq;
      throw new Error(`${who}: «${ast.name}» — не прямая с панели`);
    }
    throw new Error(`${who}: нужна прямая, заданная буквой с панели`);
  }

  // meet(объект, объект) — пересечение, посчитанное НАМИ.
  //
  // Отмечать пересечение мышью удобнее, но на длинных построениях GeoGebra
  // встаёт, вычисляя его сама: вкладка перестаёт отвечать, точка не появляется
  // нигде, и наш код при этом даже не запускается — панель честно показывает
  // свои триста миллисекунд. Наш бюджет туда не дотягивается, потому что
  // считает не наш код.
  //
  // Эта команда обходит GeoGebra целиком: ответ считает движок и кладёт в
  // таблицу. Если вдобавок выключить рисование, чертежа она не касается вовсе —
  // и тогда посчитать можно то, что мышью просто не отметить.
  #buildMeet(ggbApplet, command, key) {
    const [first, second] = command.args.map(ast => this.#panelObject(ast, 'meet'));

    let solved;
    if (first.line && second.line) {
      const point = LineEq.intersect(first.line, second.line);
      return [this.#emitPoint(ggbApplet, command, `${key}#0`, point, 'пересечение прямых')];
    }
    if (first.circle && second.circle) {
      solved = lineMeetsCircleExtended(CircleEq.radicalAxis(first.circle, second.circle),
        first.circle, this.#knownPoints(), `t${this.extCount + 1}`);
    } else {
      const line = first.line ?? second.line;
      const circle = first.circle ?? second.circle;
      solved = lineMeetsCircleExtended(line, circle, this.#knownPoints(), `t${this.extCount + 1}`);
    }

    if (solved.roots.length === 0) {
      throw new Error(`meet: ${QUADRATIC_EXCUSE[solved.kind] ?? 'пересечение не выражается'}`);
    }
    if (solved.ext) this.extCount++;

    return solved.roots.map((root, index) => this.#emitPoint(
      ggbApplet, command, `${key}#${index}`, root,
      solved.roots.length === 1 ? 'касание' : 'точка пересечения'));
  }

  // Объект панели по букве: прямая или окружность.
  #panelObject(ast, who) {
    if (ast.t === 'name') {
      const line = this.lineDefs.get(ast.name);
      if (line) return { line: line.eq };
      const circle = this.circleDefs.get(ast.name);
      if (circle) return { circle };
      throw new Error(`${who}: «${ast.name}» — не прямая и не окружность с панели`);
    }
    throw new Error(`${who}: аргументы — буквы объектов с панели`);
  }

  // Пересечение, которое может потребовать присоединения корня.
  //
  // Тут повезло больше, чем с командой tangent: точку строит САМА GeoGebra —
  // пользователь по ней кликнул, — поэтому рисовать ничего не надо и гадать про
  // ветвь корня тоже. Мы просто ОБЪЯВЛЯЕМ эту точку нашим x. Соотношения
  // x + y = S и x·y = Q верны при любом выборе, так что выбор — соглашение.
  //
  // Второй клик по той же паре объектов даёт второй корень, S − x, и расширение
  // переиспользуется: завести на одно уравнение два независимых корня было бы и
  // расточительно, и попросту неверно — они связаны.
  #meet(ggbApplet, name, args, line, circle) {
    const key = `${args[0]}×${args[1]}`;
    let entry = this.extByPair.get(key);

    if (!entry) {
      const solved = lineMeetsCircleExtended(
        line, circle, this.#knownPoints(), `t${this.extCount + 1}`);
      // Рационально разрешимые случаи идут прежним путём: там корень выбирается
      // сверкой с чертежом, и расширение только мешало бы.
      if (solved.kind !== 'extended') {
        return this.#chooseRoot(ggbApplet, name, solved, args);
      }
      this.extCount++;
      entry = { ext: solved.ext, assigned: new Map() };
      this.extByPair.set(key, entry);
    }

    const { ext, assigned } = entry;
    if (!assigned.has(name)) {
      if (assigned.size === 0) {
        // Первая точка ОПРЕДЕЛЯЕТ корень: она уже стоит на чертеже, и через неё
        // выражается всё остальное — никакого sqrt в определениях не появится.
        ext.ggbRoot = `((ToComplex(${name}) - ToComplex(${AUX_PREFIX}O)) / ${AUX_PREFIX}R)`;
        ext.ggbName = name;
        ext.name = name;      // формула пишется через ту точку, которую видно
        this.extensions.push(ext);
        assigned.set(name, ext.root());
      } else if (assigned.size === 1) {
        assigned.set(name, ext.other());
      } else {
        return { problem: 'у этой пары объектов уже взяты оба корня' };
      }
    }
    return { result: assigned.get(name) };
  }

  // Присоединённый корень на чертеже.
  //
  // Радикал сюда не годится: какую из двух ветвей возьмёт GeoGebra у
  // sqrt(S²−4Q), неизвестно. Но радикал и не нужен — x по построению есть
  // пересечение прямой с окружностью, а пересекать GeoGebra умеет сама. Рисуем
  // эту пару служебными объектами, берём Intersect(..., 1) и ОБЪЯВЛЯЕМ его
  // нашим x. Вопрос «какой из корней наш» исчезает: x+y = S и x·y = Q верны при
  // любом выборе, значит выбор — соглашение, а не факт, требующий проверки.
  //
  // Дальше любое a + b·x выражается через уже нарисованную точку, и башня
  // расширений строится тем же способом поверх предыдущего уровня.
  // Корень строится ВИДИМОЙ точкой, а не служебной. Первая версия прятала его
  // под префикс cmpl, и получалось глухо: касательные рисовались (иногда), а
  // самих точек касания на чертеже не было вовсе — хотя спрашивают обычно
  // именно их.
  //
  // Служебной остаётся только секущая: она вспомогательная и по смыслу, и по
  // виду. Её коэффициенты живут в БАЗОВОМ поле — иначе корня бы не было.
  #realizeRoot(ggbApplet, ext, line, circleName, label, polarOf = null) {
    if (ext.ggbRoot) return true;
    const names = this.#ensureComplexFrame(ggbApplet);
    if (!names) throw new Error('чертёж ещё не даёт системы координат: нужны три вершины');
    if (!circleName) throw new Error('окружность должна быть объектом чертежа');

    // Точка с таким именем уже есть — ПЕРЕОПРЕДЕЛЯТЬ её нельзя.
    //
    // Имя команда запоминает по своему тексту, чтобы повторный запуск не плодил
    // копии. Но к этому моменту на старую точку могли уже сослаться: пользователь
    // посадил на касательную точку, провёл через неё прямую. Переопределение
    // тогда замыкает граф зависимостей, и GeoGebra уходит искать цикл — у неё
    // это заняло ДВЕ МИНУТЫ полной неотзывчивости, после чего она ответила
    // «зацикливающееся определение», а построение осталось сломанным.
    //
    // Наш бюджет там бессилен: пока GeoGebra ищет цикл, наш код не выполняется
    // вовсе. Единственное лечение — не создавать цикла: раз точка уже стоит и
    // построена тем же способом, её и берём.
    if (typeof ggbApplet.exists === 'function' && ggbApplet.exists(label)) {
      ext.ggbRoot = `((ToComplex(${label}) - ToComplex(${AUX_PREFIX}O)) / ${AUX_PREFIX}R)`;
      ext.ggbName = label;
      ext.name = label;
      this.extensions.push(ext);
      return true;
    }

    const n = ++this.extCount;
    const lineLabel = `${AUX_PREFIX}Cut${n}`;

    // Секущая — это ПОЛЯРА внешней точки, а у GeoGebra для неё есть родная
    // команда. Берём её, когда точка на чертеже названа: «Polar(D,k)» против
    // пары ToPoint(...) с выражением на сотни знаков. Разница не в красоте —
    // наши определения разворачиваются до вершин и растут в сотни раз на
    // нескольких шагах, после чего GeoGebra встаёт на своём же пересчёте.
    const nativePolar = polarOf && circleName ? `Polar(${polarOf},${circleName})` : null;
    if (nativePolar) {
      if (!ggbApplet.evalCommand(`${lineLabel}=${nativePolar}`)) {
        throw new Error(`GeoGebra не приняла ${lineLabel}=${nativePolar}`);
      }
      // СЕКУЩАЯ ПОПАДАЕТ В СЛЕД, ХОТЯ И СЛУЖЕБНАЯ.
      //
      // Точки касания движок выражает через неё: T1 = Intersect(d, cmplCut1, 1).
      // Генератор служебные объекты пропускает — и правильно делает, — но тогда
      // у точки касания пропадает аргумент, и она не строится вовсе, а следом и
      // всё, что на ней стоит. Между тем секущая эта — поляра, объект вполне
      // геометрический, и генератор её строить умеет. Записываем её в след: он
      // сам решит, показывать её или нет (см. from-bridge.js).
      this.trace.push({ name: lineLabel, type: 'line', cmd: nativePolar,
                        parsed: parseCommand(nativePolar) });
    } else {
      const seed = line.beta.equals(this.ring.one()) ? this.ring.i() : this.ring.one();
      const at = expr => `ToPoint(ToComplex(${AUX_PREFIX}O) + ${AUX_PREFIX}R*${valueToGgb(expr, names)})`;
      const first = at(line.rhs().div(2n));
      const second = at(seed.add(line.reflect(seed)).div(2n));
      if (!ggbApplet.evalCommand(`${lineLabel}=Line(${first},${second})`)) {
        throw new Error('GeoGebra не приняла определение секущей');
      }
    }
    this.auxObjects.add(lineLabel);
    ggbApplet.evalCommand(`SetVisibleInView(${lineLabel},1,false)`);

    if (!ggbApplet.evalCommand(`${label}=Intersect(${circleName},${lineLabel},1)`)) {
      throw new Error(`GeoGebra не смогла построить ${label}=Intersect(${circleName},${lineLabel},1)`);
    }
    // Пересечения может не быть НА САМОМ ДЕЛЕ: из точки внутри окружности
    // касательных не провести. Символьно корень при этом существует (он
    // комплексный), а на чертеже точки нет — и сказать об этом надо прямо,
    // иначе выглядит как молчаливая поломка.
    if (typeof ggbApplet.isDefined === 'function' && !ggbApplet.isDefined(label)) {
      throw new Error('точек касания на чертеже нет: точка лежит внутри окружности');
    }

    // В координатах движка, то есть после нормировки z ↦ (z − O)/R.
    ext.ggbRoot = `((ToComplex(${label}) - ToComplex(${AUX_PREFIX}O)) / ${AUX_PREFIX}R)`;
    ext.ggbName = label;
    // Формула должна читаться сама: раз корень стал точкой чертежа, пусть в
    // ней и стоит ЕЁ имя, а не безликая буква. «z + T1²z̄ = 2·T1» понятно
    // сразу, «z + t²z̄ = 2·t» требует держать в голове, что такое t.
    ext.name = label;
    this.extensions.push(ext);
    return true;
  }

  // Общая часть всех построений точки: имя, запись в таблицу, отрисовка.
  #emitPoint(ggbApplet, command, key, expr, why) {
    const name = this.#freshLabel(ggbApplet, command, key, 'K');
    const drawable = isDrawableValue(expr);
    this.commandPoints.set(name, { expr, source: command.source });
    this.pointExpr.set(name, expr);
    const already = typeof ggbApplet.exists === 'function' && ggbApplet.exists(name);
    if (drawable && !already) this.#placePoint(ggbApplet, name, expr);
    this.#row(name, {
      kind: 'point',
      text: expr.toString(),
      tex: expr.toTex(),
      note: drawable
        ? `${why}: ${command.source}`
        : `${why}: ${command.source} — иррациональна, на чертёж не ставится`,
      check: drawable
        ? this.#verify(this.#numericContext(ggbApplet), ggbApplet, name, expr)
        : undefined,
    });
    return { name, text: expr.toString(), tex: expr.toTex() };
  }

  // native — готовая команда GeoGebra («Tangent(T_1,k)»). Когда она есть, брать
  // надо именно её: наши определения разворачиваются до вершин a, b, c и растут
  // в сотни раз на нескольких шагах, а родная команда коротка, и считает её
  // GeoGebra своим алгоритмом. Уравнение в таблице при этом всё равно наше.
  #emitLine(ggbApplet, command, key, eq, why, native = null) {
    const name = this.#freshLabel(ggbApplet, command, key, 'l');
    const drawable = native
      ? this.drawing
      : isDrawableValue(eq.beta) && isDrawableValue(eq.gamma);
    this.commandLines.set(name, { eq, source: command.source });
    this.lineDefs.set(name, { p: null, q: null, eq });
    // Объект уже стоит — не переопределяем: на него могли сослаться, и
    // переопределение замыкает граф зависимостей (см. #realizeRoot).
    const already = typeof ggbApplet.exists === 'function' && ggbApplet.exists(name);
    if (already) {
      // определение то же самое — команда та же, имя запомнено по её тексту
    } else if (drawable && native) {
      if (!ggbApplet.evalCommand(`${name}=${native}`)) {
        throw new Error(`GeoGebra не приняла ${name}=${native}`);
      }
    } else if (drawable) {
      this.#placeLine(ggbApplet, name, eq);
    }
    this.#row(name, {
      kind: 'line',
      text: eq.toString(),
      tex: eq.toTex(),
      canonical: drawable ? () => eq.toCanonical() : undefined,
      note: drawable
        ? `${why}: ${command.source}`
        : `${why}: ${command.source} — коэффициенты иррациональны, на чертёж не ставится`,
    });
    return { name, text: eq.toString(), tex: eq.toTex() };
  }

  // Окружность по букве с панели. В отличие от radline, точка тут не годится:
  // и у гомотетии, и у касательной точка вырождает задачу в бессмыслицу.
  #namedCircle(ast, who) {
    if (ast.t === 'name') {
      const circ = this.circleDefs.get(ast.name);
      if (circ) return circ;
      throw new Error(`${who}: «${ast.name}» — не окружность с панели`);
    }
    throw new Error(`${who}: нужна окружность, заданная буквой с панели`);
  }

  // Аргумент радикальной оси: либо окружность с панели по имени, либо точка,
  // то есть окружность нулевого радиуса — формула оси от этого не меняется.
  #asCircle(ast, ctx) {
    if (ast.t === 'name') {
      const circ = this.circleDefs.get(ast.name);
      if (circ) return circ;
      if (this.lineDefs.has(ast.name)) {
        throw new Error(`radline: «${ast.name}» — прямая, а нужна точка или окружность`);
      }
    }
    return new CircleEq(evalAst(ast, ctx), this.ring.zero());
  }

  // Из общего вида A·z + B·z̄ + C = 0 в нормированный. Заодно проверяем, что
  // это вообще прямая на плоскости: у настоящей |β| = 1 и δ = β·δ̄, иначе
  // уравнение и сопряжённое ему задают разные прямые, то есть ни одной.
  #lineFromCoefficients([A, B, C]) {
    if (A.isZero()) throw new Error('buildline: коэффициент при z нулевой — это не прямая');
    const eq = new LineEq(B.div(A), C.div(A));
    if (!eq.beta.mul(eq.beta.conjugate()).equals(this.ring.one())) {
      throw new Error('buildline: |B/A| ≠ 1 — такое уравнение не задаёт прямую на плоскости');
    }
    if (!eq.gamma.equals(eq.beta.mul(eq.gamma.conjugate()))) {
      throw new Error('buildline: свободный член не согласован с сопряжением — уравнение пустое');
    }
    return eq;
  }

  // Рисует прямую по её уравнению: берём на ней две точки и отдаём GeoGebra
  // обычную команду Line. Точка δ/2 лежит на прямой всегда (это следует из
  // δ = β·δ̄), вторая — середина между пробной точкой и её отражением; пробную
  // берём так, чтобы она не совпала с первой.
  #placeLine(ggbApplet, name, eq) {
    if (!this.drawing) return false;
    const names = this.#ensureComplexFrame(ggbApplet);
    if (!names) return false;
    const seed = eq.beta.equals(this.ring.one()) ? this.ring.i() : this.ring.one();
    const first = eq.rhs().div(2n);
    const second = seed.add(eq.reflect(seed)).div(2n);
    const at = expr => `ToPoint(ToComplex(${AUX_PREFIX}O) + ${AUX_PREFIX}R*${valueToGgb(expr, names)})`;
    if (!ggbApplet.evalCommand(`${name}=Line(${at(first)},${at(second)})`)) {
      throw new Error('GeoGebra не приняла определение прямой');
    }
    return true;
  }

  // Вспомогательные объекты, через которые чертёж переводится в систему
  // координат движка: центр описанной, её радиус и нормированный комплексный
  // образ каждой образующей. Создаются один раз, прячутся с глаз и
  // пропускаются мостом (см. AUX_PREFIX).
  #ensureComplexFrame(ggbApplet) {
    if (typeof ggbApplet?.evalCommand !== 'function') return null;
    if (this.unitObjects.length < 3) return null;
    const [A, B, Cv] = this.unitObjects;

    const define = (label, definition) => {
      if (this.auxObjects.has(label)) return;
      if (!ggbApplet.evalCommand(`${label}=${definition}`)) {
        throw new Error(`GeoGebra не приняла определение ${label}`);
      }
      this.auxObjects.add(label);
      ggbApplet.evalCommand(`SetVisibleInView(${label},1,false)`);
      ggbApplet.evalCommand(`ShowLabel(${label},false)`);
    };

    define(`${AUX_PREFIX}O`, `Center(Circle(${A},${B},${Cv}))`);
    define(`${AUX_PREFIX}R`, `Distance(${AUX_PREFIX}O,${A})`);

    const names = [];
    for (let v = 0; v < this.ring.size; v++) {
      const src = this.varSource[v];
      if (!src) return null;
      const label = `${AUX_PREFIX}${src.obj}`;
      // (ToComplex(P) − ToComplex(O)) / R — та же нормировка z ↦ (z−O)/R,
      // что и в численной сверке, только выраженная средствами GeoGebra
      define(label, `(ToComplex(${src.obj})-ToComplex(${AUX_PREFIX}O))/${AUX_PREFIX}R`);
      names[v] = src.conj ? `conjugate(${label})` : label;
    }
    return names;
  }

  // Ставит найденную точку на чертёж НАСТОЯЩИМ определением через A, B, C.
  // Тогда это обычная зависимая точка GeoGebra: её видно, её можно выделять и
  // брать в дальнейшие построения, она сама едет за вершинами и переживает
  // сохранение файла.
  #placePoint(ggbApplet, name, expr) {
    // Рисование выключено — считаем и показываем, но чертёж не трогаем.
    if (!this.drawing) return false;
    const names = this.#ensureComplexFrame(ggbApplet);
    if (!names) return false;
    const body = valueToGgb(expr, names);
    const definition =
      `ToPoint(ToComplex(${AUX_PREFIX}O) + ${AUX_PREFIX}R*${body})`;
    if (!ggbApplet.evalCommand(`${name}=${definition}`)) {
      throw new Error('GeoGebra не приняла определение точки');
    }
    return true;
  }

  // ---- пользовательские выражения -----------------------------------------

  // Считает выражения от координат построенных точек: P - Q, (X-Y)/(X-Z) и так
  // далее. Каждая строка независима, ошибка в одной не мешает остальным.
  evaluate(text) {
    const env = new Map(this.pointExpr);
    for (const [name, value] of this.userVars) env.set(name, value);
    const objects = this.#objectEnv();

    const results = [];
    String(text ?? '').split('\n').forEach((source, index) => {
      if (!source.trim() || source.trim().startsWith('#')) return;
      try {
        const out = withComputeBudget(ComplanatorBridge.COMPUTE_BUDGET_MS,
          () => evaluateLine(source, env, this.ring, objects));
        if (!out) return;
        if (out.target) {
          this.userVars.set(out.target, out.value);
          env.set(out.target, out.value);
        }
        results.push({
          line: index + 1,
          source: source.trim(),
          target: out.target,
          text: out.value.toString(),
          tex: out.value.toTex(),
          nature: out.nature,
          // Полное разложение — ПО ТРЕБОВАНИЮ. В строке печатается дешёвое и
          // неполное (оно зовётся на каждый счёт), а это вправе думать
          // секунды, потому что его попросили явно.
          factor: () => withComputeBudget(ComplanatorBridge.EXTENDED_BUDGET_MS, () => {
            const rnd = makeSeededRandom(index + 1);
            const tex = fullyFactored(out.value, true, rnd);
            const text = fullyFactored(out.value, false, makeSeededRandom(index + 1));
            return tex && text ? { tex, text } : null;
          }),
        });
        // Само значение — наружу: по нему панель строит ГМТ. Поле СКРЫТОЕ: в нём
        // ссылка на кольцо, и JSON.stringify по такому объекту зациклится, а
        // строки результата сериализуют и тесты, и отчёты.
        Object.defineProperty(results[results.length - 1], 'value',
          { value: out.value, enumerable: false });
      } catch (e) {
        results.push({ line: index + 1, source: source.trim(), error: e.message });
      }
    });
    return results;
  }

  // Условие на точки: строка из тех же команд, что и в командной строке, но
  // неизвестных в ней нет — все точки уже построены. Ответ не «где точка», а
  // «при каких вершинах написанное выполняется»: уравнение прямо через a, b, c.
  //
  // Пользовательские переменные из строки выражений сюда тоже пускаем: если
  // где-то уже посчитана точка, писать её заново незачем.
  conditions(text) {
    const env = new Map(this.pointExpr);
    for (const [name, value] of this.userVars) env.set(name, value);

    const results = [];
    for (const line of parseProgram(text)) {
      if (line.error) {
        results.push({ line: line.index + 1, source: line.source.trim(), error: line.error });
        continue;
      }
      try {
        const found = withComputeBudget(ComplanatorBridge.COMPUTE_BUDGET_MS,
          () => conditionEquations(line.commands, env));
        for (const item of found) {
          results.push({
            line: line.index + 1,
            source: item.command.source,
            identity: item.identity,
            impossible: item.impossible,

            text: item.identity ? '0' : item.equation.toString(),
            tex: item.identity ? '0' : item.equation.toTex(),
            // Полное разложение — по кнопке, как в строке выражений: печатается
            // дешёвое и неполное, а общий множитель двух условий виден только в
            // полном.
            factor: item.identity || item.impossible ? null
              : () => withComputeBudget(ComplanatorBridge.EXTENDED_BUDGET_MS, () => {
                const tex = fullyFactored(item.equation, true, makeSeededRandom(line.index + 1));
                const text = fullyFactored(item.equation, false, makeSeededRandom(line.index + 1));
                return tex && text ? { tex, text } : null;
              }),
          });
          Object.defineProperty(results[results.length - 1], 'value',
            { value: item.identity ? null : item.equation, enumerable: false });
        }
      } catch (e) {
        results.push({ line: line.index + 1, source: line.source.trim(), error: e.message });
      }
    }
    return results;
  }

  // ---- сверка с чертежом --------------------------------------------------

  // Численные значения всех образующих в той системе координат, в которой
  // считает движок. null, если апплет координат не даёт (тесты) или вершины
  // выродились в прямую.
  #numericContext(ggbApplet) {
    if (typeof ggbApplet?.getXcoord !== 'function' || this.unitObjects.length < 3) return null;
    const raw = n => C.of(ggbApplet.getXcoord(n), ggbApplet.getYcoord(n));
    const pts = this.unitObjects.map(raw);
    const frame = circumFrame(...pts);
    if (!frame) return null;
    const { norm, denorm } = frame;
    const values = [];
    for (let i = 0; i < this.ring.size; i++) {
      const src = this.varSource[i];
      // Буква точки локуса — единственная в кольце, за которой не стоит объект
      // чертежа: она обозначает не построенную точку, а произвольную точку
      // кривой. Координат у неё нет и быть не может, и они не нужны — из
      // уравнения она уходит раньше, чем доходит до чисел. Отказываться из-за
      // неё от всей численной сверки нельзя: тогда ни одна кривая не нарисуется.
      if (!src && (i === this.locusVar || i === this.locusVar + 1)) {
        values[i] = C.of(NaN, NaN);
        continue;
      }
      if (!src) return null;
      const z = norm(raw(src.obj));
      values[i] = src.conj ? C.conj(z) : z;
    }
    // Присоединённые корни численно берутся с чертежа: каждый из них — реальная
    // точка GeoGebra, поэтому радикал вычислять не надо, и вопрос «какая ветвь»
    // не возникает даже здесь.
    for (const ext of this.extensions) {
      if (ext.ggbName) ext.numericRoot = norm(raw(ext.ggbName));
    }
    return { values, norm, denorm, raw, radius: frame.radius };
  }

  // Прямая чертежа тройкой коэффициентов a·x + b·y + c = 0.
  #lineCoefficients(ggbApplet, name) {
    if (typeof ggbApplet?.getZcoord !== 'function') return null;
    const a = ggbApplet.getXcoord(name);
    const b = ggbApplet.getYcoord(name);
    const c = ggbApplet.getZcoord(name);
    return [a, b, c].every(Number.isFinite) ? { a, b, c } : null;
  }

  // Живая проверка: символьный ответ обязан совпасть с настоящим положением
  // точки на чертеже. Именно такая сверка показала бы в браузере тот баг со
  // знаком в intersectLines, который в своё время поймал только тест.
  #verify(ctx, ggbApplet, name, expr) {
    if (!ctx) return null;
    const got = expr.evalFloat(ctx.values);
    const target = ctx.norm(ctx.raw(name));
    if (!C.isFinite(got) || !C.isFinite(target)) return null;
    // Если оба ушли в бесконечность, чертёж вырожден (инверсия центра, точка
    // пересечения параллельных) — это не расхождение, а свойство картинки.
    if (C.abs(got) > DEGENERATE_SCALE && C.abs(target) > DEGENERATE_SCALE) {
      return 'на этом чертеже конфигурация вырождена — символьный ответ всё равно верен';
    }
    // Сравниваем относительную погрешность: у больших координат абсолютная
    // разница набегает сама собой.
    const d = C.abs(C.sub(got, target)) / Math.max(1, C.abs(target));
    if (d <= CHECK_TOLERANCE) return null;
    return `расхождение с чертежом: ${d.toExponential(1)}`;
  }

  #handleFreePoint(name) {
    this.#generator(name, () => {
      const idx = this.freeOrder.length;
      this.freeOrder.push(name);
      if (idx < TRIANGLE_LETTERS.length) {
        const letter = TRIANGLE_LETTERS[idx];
        this.usedLetters.add(letter);
        return { expr: this.ring.unitPoint(letter), letter, unit: true };
      }
      // Четвёртая и далее свободная точка ничем не связана: заводим ДВЕ
      // образующие, саму точку и её сопряжённую.
      const letter = this.#takeLetter();
      return { expr: this.ring.freePoint(letter), letter, unit: false };
    });
    this.#emitGenerator(name);
  }

  #emitGenerator(name) {
    const g = this.generators.get(name);
    this.#row(name, {
      kind: 'free',
      text: g.expr.toString(),
      tex: g.expr.toTex(),
      // для несвободных образующих показываем само правило сопряжения —
      // именно оно объясняет, почему в ответах не появляется лишних букв
      note: g.unit ? null : this.ring.describeConj(g.letter),
    });
  }

  // ---- точки --------------------------------------------------------------

  // ОБЪЕКТ, КОТОРОГО ДВИЖОК НЕ ВЫРАЖАЕТ, ВСЁ РАВНО ЗАПИСЫВАЕТСЯ В СЛЕД.
  //
  // Дуга, полуокружность, вектор, сектор — движку их не выразить, и раньше
  // они не оставляли по себе никакой памяти: ни строки, ни следа. А след
  // читает ГЕНЕРАТОР, который считает числами и которому дуга не помеха: он
  // возьмёт её несущую окружность, а вектор — как прямую. Из-за пустоты в
  // следе он не видел ни самого объекта, ни всего, что на нём стоит: точка,
  // посаженная на полуокружность, оказывалась свободной точкой плоскости.
  //
  // Поэтому пишем след ВСЕГДА, с настоящим типом от GeoGebra, — а уж что с
  // ним делать, решает тот, кто читает.
  #noteForeign(ggbApplet, name, type) {
    const cmd = readCommand(ggbApplet, name);
    this.trace.push({ name, type, cmd, parsed: parseCommand(cmd) });
  }

  #handlePoint(ggbApplet, name) {
    // Своя точка из командной строки: выражение уже посчитано, заново её
    // образующей делать нельзя.
    const fromCommand = this.commandPoints.get(name);
    if (fromCommand) {
      this.pointExpr.set(name, fromCommand.expr);
      this.#row(name, {
        kind: 'point',
        text: fromCommand.expr.toString(),
        tex: fromCommand.expr.toTex(),
        note: fromCommand.note ?? `из командной строки: ${fromCommand.source}`,
        check: this.#verify(this.#numericContext(ggbApplet), ggbApplet, name, fromCommand.expr),
      });
      return;
    }

    const cmd = readCommand(ggbApplet, name);
    if (isFreePoint(ggbApplet, name, cmd)) { this.#handleFreePoint(name); return; }

    const parsed = parseCommand(cmd);
    this.trace.push({ name, type: 'point', cmd, parsed });
    if (!parsed) {
      this.#row(name, { kind: 'unsupported', text: `не удалось разобрать команду: ${cmd}`, raw: cmd });
      return;
    }
    const { name: cname, args } = parsed;
    const point = n => this.pointExpr.get(n);
    let result = null;
    let problem = null;
    // Оговорка к ВЕРНОМУ ответу — не то же самое, что отказ. Нужна там, где
    // движок и GeoGebra считают РАЗНОЕ по существу, а не по ошибке.
    let caveat = null;

    if (cname === 'Point' && args.length >= 1) {
      // Точка, посаженная на объект: она произвольна, но её сопряжённая
      // выражается через неё саму — правило берётся у объекта (см. ring.js).
      if (this.#pointOnPath(name, args[0])) { this.#emitGenerator(name); return; }
      problem = `Point: «${args[0]}» — не прямая и не окружность с известным уравнением`;
    } else if (cname === 'Midpoint' && args.length === 2) {
      const [p, q] = args.map(point);
      if (p && q) result = F.midpoint(p, q);
    } else if (cname === 'Midpoint' && args.length === 1) {
      const seg = this.lineDefs.get(args[0]);
      if (seg) result = F.midpoint(seg.p, seg.q);
    } else if (cname === 'Intersect' && args.length >= 2) {
      const l1 = this.lineDefs.get(args[0]), l2 = this.lineDefs.get(args[1]);
      const k1 = this.circleDefs.get(args[0]), k2 = this.circleDefs.get(args[1]);
      if (l1 && l2) result = LineEq.intersect(l1.eq, l2.eq);
      else if ((l1 && k2) || (k1 && l2)) {
        ({ result, problem } = this.#meet(ggbApplet, name, args, (l1 ?? l2).eq, k1 ?? k2));
      } else if (k1 && k2) {
        // Пересечение двух окружностей — это их радикальная ось и любая из них.
        ({ result, problem } = this.#meet(ggbApplet, name, args,
          CircleEq.radicalAxis(k1, k2), k1));
      }
    } else if (cname === 'Reflect' && args.length === 2) {
      const z = point(args[0]);
      if (z && this.pointExpr.has(args[1])) result = F.reflectOverPoint(z, point(args[1]));
      else if (z && this.lineDefs.has(args[1])) {
        result = this.lineDefs.get(args[1]).eq.reflect(z);
      } else if (z && this.circleDefs.has(args[1])) {
        // Инверсия рациональна: z ↦ o + r²/conj(z−o). Радикалы тут ни при чём.
        result = this.circleDefs.get(args[1]).invert(z);
      }
    } else if (cname === 'Dilate' || cname === 'Rotate') {
      // Центр обязателен. Без него GeoGebra берёт СВОЁ начало координат, а у
      // движка ноль — это центр описанной окружности; точки разные, и молча
      // подставить ноль значило бы соврать.
      if (args.length < 3) {
        problem = `${cname}: нужен явный центр — начало координат GeoGebra движку неизвестно`;
      } else {
        const z = point(args[0]);
        const center = point(args[2]);
        if (z && center && cname === 'Dilate') {
          const ratio = parseExactRatio(args[1]);
          if (ratio) {
            result = F.dilate(z, this.ring.constant(new CFrac(new Fraction(ratio.n, ratio.d))), center);
          } else {
            problem = `Dilate: коэффициент «${args[1]}» не точная дробь — движок работает только с рациональными`;
          }
        } else if (z && center) {
          // Кратные 90° идут прежней дорогой: она не заводит расширения вовсе,
          // а значит и не удорожает всё, что строится дальше.
          const quarters = parseQuarterTurns(args[1]);
          if (quarters !== null) result = F.rotateQuarter(z, quarters, center);
          else {
            const turn = parseTurnFraction(args[1]);
            if (!turn) {
              problem = `Rotate: угол «${args[1]}» не удалось прочитать как долю оборота`;
            } else if (turn.d > 1000n) {
              problem = `Rotate: угол «${args[1]}» не похож на точную долю оборота`;
            } else {
              try {
                const zeta = rootOfUnity(this.ring, Number(turn.d));
                result = F.dilate(z, powerOf(zeta, Number(turn.n)), center);
              } catch (e) {
                problem = `Rotate: ${e.message}`;
              }
            }
          }
        }
      }
    } else if (cname === 'ClosestPoint' && args.length === 2) {
      const zName = this.pointExpr.has(args[0]) ? args[0] : args[1];
      const lineName = this.lineDefs.has(args[0]) ? args[0] : args[1];
      const z = point(zName);
      const line = this.lineDefs.get(lineName);
      if (z && line) {
        result = line.eq.project(z);
        // У ОТРЕЗКА и ЛУЧА GeoGebra прижимает ответ к ближнему концу, а движок
        // честно проецирует на всю прямую. Оба ответа правильные — просто это
        // разные задачи, и при тупом угле точки на чертеже действительно
        // разные. Молчать здесь нельзя: живая сверка покажет расхождение, и
        // без объяснения оно читается как ошибка движка.
        const kind = this.lineKind.get(lineName);
        if (kind === 'segment' || kind === 'ray') {
          caveat = `${lineName} — это ${kind === 'segment' ? 'отрезок' : 'луч'}: `
            + 'движок проецирует на всю прямую, а GeoGebra прижимает к концу. '
            + 'Если основание перпендикуляра вне отрезка, точки разойдутся — и это не ошибка';
        }
      }
    } else if (cname === 'Center' && args.length === 1) {
      const circ = this.circleDefs.get(args[0]);
      if (circ) result = circ.center;
    } else if (cname === 'Centroid' && args.length === 1) {
      // Осторожно: GeoGebra считает центроид ПЛОЩАДИ (формула шнурков,
      // AlgoPolygon#calcCentroid), а не среднее вершин. Для треугольника это
      // одно и то же, дальше — уже нет.
      const verts = this.polyDefs.get(args[0]);
      if (verts && verts.length === 3) {
        const pts = verts.map(point);
        if (pts.every(Boolean)) result = pts[0].add(pts[1]).add(pts[2]).div(3n);
      } else if (verts) {
        problem = 'Centroid: у GeoGebra это центроид площади, а не вершин — совпадают только для треугольника';
      }
    } else if (cname === 'TriangleCenter' && args.length === 4) {
      const pts = args.slice(0, 3).map(point);
      const build = TRIANGLE_CENTERS[Number(args[3])];
      if (pts.every(Boolean) && build) result = build(...pts);
      else if (pts.every(Boolean)) {
        problem = `X(${args[3]}) — не выражается рационально через образующие: такие центры зависят от длин сторон, а это радикалы`;
      }
    }

    if (result) {
      this.pointExpr.set(name, result);
      this.#row(name, {
        kind: 'point',
        text: result.toString(),
        tex: result.toTex(),
        check: this.#verify(this.#numericContext(ggbApplet), ggbApplet, name, result),
        note: caveat,
        raw: cmd,
      });
      return;
    }
    this.pointExpr.delete(name);
    this.#row(name, { kind: 'unsupported', text: problem ?? this.#diagnose(cname, args), raw: cmd });
  }

  // Кандидаты в «уже известные корни» для Виета — все построенные точки.
  // Порядок — порядок построения, то есть вершины проверяются первыми.
  #knownPoints() { return [...this.pointExpr.values()]; }

  // У квадратного уравнения два корня, а GeoGebra спрашивает про конкретную
  // точку. Различаем численно: подставляем настоящие координаты чертежа и
  // смотрим, к какому корню точка ближе. Индекс из Intersect[f, k, 2] служит
  // запасным вариантом, когда координат нет.
  #chooseRoot(ggbApplet, name, solved, args) {
    if (solved.roots.length === 0) {
      return { result: null, problem: QUADRATIC_EXCUSE[solved.kind] ?? 'уравнение не решилось' };
    }
    if (solved.roots.length === 1) return { result: solved.roots[0], problem: null };

    const ctx = this.#numericContext(ggbApplet);
    if (ctx) {
      const target = ctx.norm(ctx.raw(name));
      if (C.isFinite(target)) {
        const i = nearestIndex(solved.roots.map(r => r.evalFloat(ctx.values)), target);
        if (i >= 0) return { result: solved.roots[i], problem: null };
      }
    }
    const index = Number(args[2]);
    return { result: solved.roots[index === 2 ? 1 : 0], problem: null };
  }

  // Касательные, которые провела САМА GeoGebra (инструмент «Касательная» или
  // команда Tangent в её строке ввода).
  //
  // Здесь стоял отказ «точки касания требуют радикалов». Он устарел в тот день,
  // когда заработали квадратичные расширения: команда tangent(P,k) строит
  // ровно эти же касательные (#buildTangents), и алгебра у обоих путей одна.
  // Разница только в том, КТО рисует, — и из неё берётся единственная новая
  // задача. Там рисуем мы и потому знаем, какая прямая какому корню отвечает;
  // здесь рисует GeoGebra, и приходят два отдельных объекта с одинаковым
  // определением Tangent[P,k]. Который из них который — знает только чертёж.
  //
  // Спрашиваем у него так же, как #chooseRoot спрашивает про точку: численно.
  // Точка касания лежит на своей касательной, а до чужой от неё целая хорда,
  // так что разделение уверенное, а не на грани погрешности.
  //
  // Возвращает текст проблемы или null, если всё получилось.
  #tangentFromOutside(ggbApplet, name, { pointName, circleName, P, circ, cmd }) {
    const key = `${pointName}×${circleName}`;
    let entry = this.tangentByPair.get(key);

    if (!entry) {
      const polar = circ.polarLine(P);
      const solved = lineMeetsCircleExtended(
        polar, circ, this.#knownPoints(), `t${this.extCount + 1}`);
      if (solved.roots.length === 0) {
        return QUADRATIC_EXCUSE[solved.kind] ?? 'точки касания через a, b, c не выражаются';
      }
      // Иррациональную точку касания надо ПОСТАВИТЬ НА ЧЕРТЁЖ. Не ради красоты:
      // через неё выражается всё остальное, и она же даёт корню численное
      // значение, без которого нечем сверять ответ с картинкой. Секущая при
      // этом — поляра внешней точки, у GeoGebra для неё есть родная команда,
      // и #realizeRoot её возьмёт, раз точка на чертеже названа.
      if (solved.ext) {
        if (!this.drawing) {
          return 'точки касания иррациональны — их надо построить, '
            + 'а рисование выключено';
        }
        const label = this.#builtRoot(ggbApplet, pointName, circleName)
          ?? this.#pickName(ggbApplet, `tangent:${key}`, 'T');
        try {
          this.#realizeRoot(ggbApplet, solved.ext, polar, circleName, label, pointName);
        } catch (e) {
          // Не уложились в бюджет — это не про касательную, это про время:
          // такое обязано дойти до общего обработчика и стать строкой
          // «не посчитано». Всё остальное — честная причина отказа.
          if (e instanceof BudgetExceeded) throw e;
          return e.message;
        }
        const touch = solved.roots[0];
        // Помним как своё построение: иначе следующее же обновление чертежа
        // разберёт её как обычный Intersect по служебной секущей, а служебных
        // объектов мост не видит — и строка испортилась бы.
        this.commandPoints.set(label, {
          expr: touch, source: cmd, note: `точка касания: ${cmd}`,
        });
        this.pointExpr.set(label, touch);
        this.#row(label, {
          kind: 'point', text: touch.toString(), tex: touch.toTex(),
          note: `точка касания: ${cmd}`,
        });
      }
      entry = { roots: solved.roots, assigned: new Map() };
      this.tangentByPair.set(key, entry);
    }

    const root = this.#tangentRoot(ggbApplet, name, entry);
    if (!root) return 'у этой пары «точка — окружность» обе касательные уже разобраны';
    this.#setLineEq(name, circ.polarLine(root), cmd);
    return null;
  }

  // Точка касания, которую мы построили в ПРОШЛОЙ жизни этого построения.
  //
  // Пересборка (удалили образующую) сбрасывает кольцо и всю память моста, а
  // чертёж остаётся как был. Не узнав свою точку, мост взял бы следующее
  // свободное имя — и на чертеже завелась бы вторая такая же точка, а первая
  // осталась бы сиротой со строкой «нет символьного определения». Проверено:
  // ровно так и происходило.
  //
  // Узнаём по определению, а не по имени: наш корень — это пересечение той же
  // окружности с нашей же служебной секущей, а секущая — поляра той же точки.
  #builtRoot(ggbApplet, pointName, circleName) {
    if (typeof ggbApplet?.getAllObjectNames !== 'function') return null;
    const definition = n => parseCommand(readCommand(ggbApplet, n));
    for (const candidate of ggbApplet.getAllObjectNames()) {
      if (ggbApplet.getObjectType?.(candidate) !== 'point') continue;
      const meet = definition(candidate);
      if (!meet || meet.name !== 'Intersect') continue;
      const [circle, cut] = meet.args;
      if (circle !== circleName || !cut?.startsWith(AUX_PREFIX)) continue;
      const secant = definition(cut);
      if (secant?.name === 'Polar' && secant.args[0] === pointName) return candidate;
    }
    return null;
  }

  // Какой из двух точек касания отвечает пришедшая прямая.
  //
  // Решается ОДИН раз и запоминается. Соблазн пересопоставлять на каждом
  // обновлении велик (страховка от того, что GeoGebra переставит свои прямые
  // местами), но так делать нельзя, и это измерено в живом апплете: при
  // перетаскивании внешней точки обновления приходят в порядке
  //
  //     D → f → g → cmplCut1 → T1,
  //
  // то есть в тот момент, когда мост считает касательные, точка касания ещё
  // держит СТАРЫЕ координаты. На мелком движении это незаметно (до своей
  // прямой всё равно ближе, чем до чужой), а на скачке устаревшая точка
  // оказывается ближе к чужой — и сопоставление переворачивается. Свежие
  // данные бывают ровно однажды: в тот заход, когда корень только что
  // построен, — на нём и решаем.
  //
  // Перестановку прямых это оставляет неприкрытой, но за перетаскиванием
  // замерено, что GeoGebra их не переставляет, а перестроение чертежа мост и
  // так пересобирает с нуля.
  #tangentRoot(ggbApplet, name, { roots, assigned }) {
    if (assigned.has(name)) return assigned.get(name);
    let index = -1;
    const line = roots.length > 1 ? this.#lineCoefficients(ggbApplet, name) : null;
    if (line) {
      const ctx = this.#numericContext(ggbApplet);
      if (ctx) {
        const away = roots.map(r => distanceToLine(line, ctx.denorm(r.evalFloat(ctx.values))));
        const best = away.indexOf(Math.min(...away));
        if (Number.isFinite(away[best])) index = best;
      }
    }
    const used = new Set(assigned.values());
    // Чертёж молчит (нет ещё системы координат, корень не посчитался численно)
    // или указал на уже занятый корень — берём по порядку появления:
    // касательных ровно две, и вторая обязана оказаться не той же, что первая.
    if (index < 0 || used.has(roots[index])) index = roots.findIndex(r => !used.has(r));
    if (index < 0) return null;
    assigned.set(name, roots[index]);
    return roots[index];
  }

  #pointOnPath(name, targetName) {
    const circ = this.circleDefs.get(targetName);
    if (circ) {
      return this.#generator(name, () => {
        const letter = this.#takeLetter();
        return { expr: this.ring.pointOnCircle(letter, circ.center, circ.r2), letter, unit: false };
      });
    }
    const line = this.lineDefs.get(targetName);
    if (line) {
      return this.#generator(name, () => {
        const letter = this.#takeLetter();
        return { expr: this.ring.pointOnLine(letter, line.eq), letter, unit: false };
      });
    }
    return null;
  }

  // Отличает "команду не знаю" от "команду знаю, но аргумент не выражен через
  // образующие" — без этого в браузере всё выглядело одинаково.
  #diagnose(cname, args) {
    const known = n => this.pointExpr.has(n) || this.lineDefs.has(n)
      || this.circleDefs.has(n) || this.polyDefs.has(n);
    const hidden = args.find(n => this.ignored.has(n));
    if (hidden) {
      return `${cname}: «${hidden}» построен при выключенном Компланаторе — `
        + 'для него нет символьного определения';
    }
    const bad = args.filter(x => /^[A-Za-z]/.test(x)).find(n => !known(n));
    return bad
      ? `${cname}: нет символьного определения для «${bad}»`
      : `${cname}(…) — пока не поддержано`;
  }

  // ---- прямые -------------------------------------------------------------

  // Канонический вид отдаётся ФУНКЦИЕЙ, а не значением: считать его — это ещё
  // одно разложение на множители, а строка перерисовывается на каждое движение
  // мыши, тогда как кнопку жмут изредка.
  #setLine(name, p, q, raw) {
    const eq = LineEq.throughPoints(p, q);
    this.lineDefs.set(name, { p, q, eq });
    this.#row(name, {
      kind: 'line', text: eq.toString(), tex: eq.toTex(), canonical: () => eq.toCanonical(), raw,
    });
  }

  // Прямая, заданная сразу уравнением (касательная, поляра, радикальная ось).
  // Двух порождающих точек у неё нет, но для пересечения прямых они нужны —
  // берём любые две через образующую с правилом "точка на прямой"... нет,
  // проще: intersectLines умеет работать и по уравнениям, поэтому храним пару
  // точек только когда они есть, а пересечение с такой прямой идёт через eq.
  // БИССЕКТРИСА УГЛА — ЧЕРЕЗ ОДИН ПРИСОЕДИНЁННЫЙ КОРЕНЬ.
  //
  // Долго считалась неподдержанной, и по делу: направление биссектрисы — это
  // сумма ЕДИНИЧНЫХ векторов сторон, а единичный вектор требует |z|, то есть
  // квадратного корня из длины. Два корня сразу — расширение четвёртой степени,
  // и движок такого не держит.
  //
  // Но прямой не нужно направление — ей нужен НАКЛОН β = −d/d̄, а он от длины
  // не зависит вовсе. Если d = |d|·e^{iθ}, то d/d̄ = e^{2iθ}, и для угла с
  // сторонами p и q (θ = (arg p + arg q)/2) это ровно
  //
  //     e^{2iθ} = pq / conj(pq),
  //
  // то есть КВАДРАТ искомого числа — величина совершенно рациональная. Значит
  // достаточно присоединить один корень y с y² = pq/conj(pq), и он вдобавок
  // лежит на единичной окружности: |pq| = |conj(pq)|. А корень на окружности
  // движок умеет — сопряжение у него 1/y, и поле остаётся квадратичным.
  //
  // Внутренняя биссектриса — это β = −y, внешняя — β = +y (перпендикуляр). Какой
  // из двух корней взят, решает ЧЕРТЁЖ: рисуется вспомогательная точка
  // O + R·y, и численный слой читает корень с неё — ровно как у середин дуг.
  #bisectorEq(ggbApplet, name, x, v, y, args) {
    const p = x.sub(v), q = y.sub(v);
    if (p.isZero() || q.isZero()) return null;
    const pq = p.mul(q);
    const w = pq.div(pq.conjugate());
    const label = this.#pickName(ggbApplet, `${name}#bis`, 'W');
    const unit = new CircleEq(this.ring.zero(), this.ring.one());
    const ext = new QuadraticExt(this.ring, this.ring.zero(), w.neg(), label)
      .setCircleRule(unit);
    if (!this.#drawBisectorRoot(ggbApplet, label, args)) return null;
    ext.ggbRoot = `((ToComplex(${label}) - ToComplex(${AUX_PREFIX}O)) / ${AUX_PREFIX}R)`;
    ext.ggbName = label;
    ext.name = label;
    this.extensions.push(ext);
    this.extCount++;
    return LineEq.throughPointWithBeta(v, ext.root().neg());
  }

  // Вспомогательная точка, с которой читается корень: O + R·y, где y — квадрат
  // единичного направления биссектрисы. Строится она самой GeoGebra, поэтому
  // вопрос «какая из двух биссектрис» решается чертежом, а не гаданием.
  #drawBisectorRoot(ggbApplet, label, args) {
    if (typeof ggbApplet?.evalCommand !== 'function') return false;
    const [x, v, y] = args;
    const u = `${AUX_PREFIX}u${this.extCount + 1}`;
    try {
      // Опорная рамка (центр и радиус нормировки) может быть ещё не заведена:
      // её создаёт рисование, а биссектрису читают раньше. Заводим сами.
      this.#ensureComplexFrame(ggbApplet);
      ggbApplet.evalCommand(`${u}=UnitVector(AngleBisector(${x},${v},${y}))`);
      // Точка O + R·y, где y = квадрат единичного направления биссектрисы.
      // Умножение пишем явно: неявное между числом и точкой GeoGebra понимает
      // не везде.
      ggbApplet.evalCommand(`${label}=${AUX_PREFIX}O + ${AUX_PREFIX}R`
        + ` * (x(${u})^2 - y(${u})^2, 2 x(${u}) y(${u}))`);
      this.auxObjects.add(u);
      this.auxObjects.add(label);
      try { ggbApplet.setVisible(u, false); } catch { /* и не надо */ }
      try { ggbApplet.setVisible(label, false); } catch { /* и не надо */ }
      return ggbApplet.exists(label);
    } catch { return false; }
  }

  #setLineEq(name, eq, raw) {
    this.lineDefs.set(name, { p: null, q: null, eq });
    this.#row(name, {
      kind: 'line', text: eq.toString(), tex: eq.toTex(), canonical: () => eq.toCanonical(), raw,
    });
  }

  #handleLine(ggbApplet, name) {
    // Своя прямая из командной строки: её определение в GeoGebra — Line по двум
    // служебным точкам, разбирать его бессмысленно, уравнение знаем только мы.
    const own = this.commandLines.get(name);
    if (own) {
      this.lineDefs.set(name, { p: null, q: null, eq: own.eq });
      this.#row(name, {
        kind: 'line',
        text: own.eq.toString(),
        tex: own.eq.toTex(),
        canonical: () => own.eq.toCanonical(),
        note: `построено: ${own.source}`,
      });
      return;
    }
    const cmd = readCommand(ggbApplet, name);
    const parsed = parseCommand(cmd);
    this.trace.push({ name, type: 'line', cmd, parsed });
    if (!parsed) {
      this.#row(name, { kind: 'unsupported', text: `не удалось разобрать команду: ${cmd}`, raw: cmd });
      return;
    }
    const { name: cname, args } = parsed;
    const point = n => this.pointExpr.get(n);

    // Сторона многоугольника приходит как Segment[B, C, poly1] — третий
    // аргумент это сам многоугольник.
    if (['Line', 'Segment', 'Ray'].includes(cname) && args.length >= 2) {
      const p = point(args[0]), q = point(args[1]);
      if (p && q) { this.#setLine(name, p, q, cmd); return; }
      // Инструмент "Параллельная прямая" даёт Line[A, f] — та же команда, но
      // вторым аргументом прямая. Направление берём у неё, точку — первую.
      const base = this.lineDefs.get(args[1]);
      if (p && base) { this.#setLineEq(name, base.eq.parallelThrough(p), cmd); return; }
    } else if (cname === 'PerpendicularLine' && args.length >= 2) {
      const A = point(args[0]);
      const base = this.lineDefs.get(args[1]);
      if (A && base) { this.#setLineEq(name, base.eq.perpendicularThrough(A), cmd); return; }
    } else if ((cname === 'Tangent' || cname === 'Polar') && args.length === 2) {
      const pointName = point(args[0]) ? args[0] : args[1];
      const circleName = this.circleDefs.has(args[0]) ? args[0] : args[1];
      const P = point(pointName);
      const circ = this.circleDefs.get(circleName);
      if (P && circ) {
        // Поляра точки; если точка лежит на окружности, это и есть касательная
        // в ней. Из внешней точки касательных две, и точки касания придётся
        // присоединить к полю — этим занимается #tangentFromOutside.
        if (cname === 'Tangent' && !circ.contains(P)) {
          const problem = this.#tangentFromOutside(ggbApplet, name,
            { pointName, circleName, P, circ, cmd });
          if (!problem) return;
          this.lineDefs.delete(name);
          this.#row(name, {
            kind: 'unsupported',
            text: `касательная из внешней точки: ${problem}`,
            raw: cmd,
          });
          return;
        }
        this.#setLineEq(name, circ.polarLine(P), cmd);
        return;
      }
    } else if (cname === 'AngleBisector' && args.length === 3) {
      const [x, v, y] = args.map(point);
      if (x && v && y) {
        const eq = this.#bisectorEq(ggbApplet, name, x, v, y, args);
        if (eq) { this.#setLineEq(name, eq, cmd); return; }
      }
    } else if (cname === 'PerpendicularBisector' && args.length >= 1) {
      const seg = args.length === 1 ? this.lineDefs.get(args[0]) : null;
      const p = seg ? seg.p : point(args[0]);
      const q = seg ? seg.q : point(args[1]);
      if (p && q) {
        const mid = F.midpoint(p, q);
        this.#setLineEq(name, LineEq.throughPoints(p, q).perpendicularThrough(mid), cmd);
        return;
      }
    }

    this.lineDefs.delete(name);
    this.#row(name, { kind: 'unsupported', text: this.#diagnose(cname, args), raw: cmd });
  }

  // ---- многоугольники -----------------------------------------------------

  // Сам многоугольник в таблицу не идёт — он нужен только чтобы знать вершины
  // (для Centroid) и чтобы Segment[B,C,poly1] был понятен.
  #handlePolygon(ggbApplet, name) {
    const parsed = parseCommand(readCommand(ggbApplet, name));
    if (parsed && parsed.name === 'Polygon') this.polyDefs.set(name, parsed.args);
  }

  // ---- окружности ---------------------------------------------------------

  // Коника с чертежа. «conic» бывает и у окружности, заданной пятью точками, —
  // тогда сперва пробуем окружность, и только если это не она, читаем конику.
  #handleConic(ggbApplet, name) {
    const cmd = readCommand(ggbApplet, name);
    const parsed = parseCommand(cmd);
    this.trace.push({ name, type: 'conic', cmd, parsed });
    if (parsed?.name === 'Circle') { this.#handleCircle(ggbApplet, name); return; }
    const args = parsed?.args ?? [];
    const pts = args.map(a => this.pointExpr.get(a));
    let eq = null;
    if (parsed?.name === 'Conic' && args.length === 5 && pts.every(Boolean)) {
      eq = ConicEq.throughFivePoints(pts);
    } else if (parsed?.name === 'Parabola' && args.length === 2 && pts[0]) {
      const line = this.lineDefs.get(args[1]);
      if (line) eq = ConicEq.parabola(pts[0], line.eq);
    } else if ((parsed?.name === 'Ellipse' || parsed?.name === 'Hyperbola')
               && args.length === 3 && pts.every(Boolean)) {
      const a2 = ConicEq.squaredAxis(pts[0], pts[1], pts[2], parsed.name === 'Hyperbola');
      if (a2) eq = ConicEq.byFociAndSquaredAxis(pts[0], pts[1], a2.value);
    }
    if (!eq) {
      this.conicDefs.delete(name);
      this.#row(name, { kind: 'unsupported', text: this.#diagnose(parsed?.name ?? 'коника', args), raw: cmd });
      return;
    }
    this.conicDefs.set(name, eq);
    this.#row(name, { kind: 'conic', text: eq.toString(), tex: eq.toTex(), raw: cmd });
  }

  // Вписанная окружность: центр на двух биссектрисах, квадрат радиуса — квадрат
  // расстояния от центра до стороны.
  #incircleEq(ggbApplet, name, args) {
    const [a, b, c] = args.map(n => this.pointExpr.get(n));
    if (!a || !b || !c) return null;
    try {
      const wa = this.#bisectorEq(ggbApplet, `${name}#wa`, b, a, c, [args[1], args[0], args[2]]);
      const wb = this.#bisectorEq(ggbApplet, `${name}#wb`, a, b, c, [args[0], args[1], args[2]]);
      if (!wa || !wb) return null;
      const centre = LineEq.intersect(wa, wb);
      // Квадрат радиуса: |I − F|², где F — проекция центра на сторону BC.
      const side = LineEq.throughPoints(b, c);
      const foot = side.project(centre);
      const d = centre.sub(foot);
      return new CircleEq(centre, d.mul(d.conjugate()));
    } catch { return null; }
  }

  #handleCircle(ggbApplet, name) {
    const cmd = readCommand(ggbApplet, name);
    const parsed = parseCommand(cmd);
    this.trace.push({ name, type: 'circle', cmd, parsed });
    // ВПИСАННАЯ ОКРУЖНОСТЬ — теперь тоже выражается.
    //
    // Центр — пересечение двух биссектрис (по одному присоединённому корню на
    // каждую, см. #bisectorEq), а вот радиус НОВОГО корня не требует вовсе:
    // CircleEq хранит его КВАДРАТ, а квадрат расстояния от центра до стороны —
    // величина рациональная. Потому вписанная окружность и оказалась доступна
    // ровно в тот момент, когда заработала биссектриса.
    if (parsed.name === 'Incircle' && parsed.args.length === 3) {
      const eq = this.#incircleEq(ggbApplet, name, parsed.args);
      if (eq) {
        this.circleDefs.set(name, eq);
        this.#row(name, {
          kind: 'circle', text: eq.toString(), tex: eq.toTex(),
          canonical: () => eq.toCanonical(), raw: cmd, note: 'вписанная окружность',
        });
        return;
      }
    }
    if (!parsed || parsed.name !== 'Circle') return;
    const { args } = parsed;
    // CircleEq хранит центр и КВАДРАТ радиуса — обе величины рациональны, тогда
    // как сам радиус нет. Этого хватает и точке на окружности, и поляре, и
    // пересечениям.
    let eq = null;
    if (args.length === 3) {
      const pts = args.map(a => this.pointExpr.get(a));
      if (pts.every(Boolean)) eq = CircleEq.throughThreePoints(...pts);
    } else if (args.length === 2) {
      const o = this.pointExpr.get(args[0]);
      const t = this.pointExpr.get(args[1]);
      if (o && t) eq = CircleEq.centerAndPoint(o, t);
      // ЦИРКУЛЬ: второй аргумент — не точка, а раствор. Перенос раствора у
      // Евклида отдельная нетривиальная конструкция, здесь же он стоит одной
      // строки: |PQ|² рационально, а больше окружности ничего и не нужно.
      else if (o) {
        const ends = compassEnds(args[1], {
          segment: n => { const seg = this.lineDefs.get(n); return seg?.p && seg?.q ? [seg.p, seg.q] : null; },
          point: n => this.pointExpr.get(n),
        });
        if (ends) eq = CircleEq.compass(ends[0], ends[1], o);
        else if (isPlainNumber(args[1])) {
          this.circleDefs.delete(name);
          this.#row(name, { kind: 'unsupported', raw: cmd,
            text: 'радиус числом не выражается: движок символьный, у него есть только'
              + ' точки чертежа. Постройте отрезок нужной длины и возьмите циркуль по нему' });
          return;
        }
      }
    }
    if (!eq) {
      this.circleDefs.delete(name);
      this.#row(name, { kind: 'unsupported', text: this.#diagnose('Circle', args), raw: cmd });
      return;
    }
    this.circleDefs.set(name, eq);
    this.#row(name, {
      kind: 'circle', text: eq.toString(), tex: eq.toTex(), canonical: () => eq.toCanonical(), raw: cmd,
    });
  }
}
