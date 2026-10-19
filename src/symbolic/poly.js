import { CFrac, ZERO, ONE } from './complex-fraction.js';
import { checkIfHeavy } from './budget.js';

// Многочлен от произвольного числа образующих, ПЛОСКОЕ разреженное
// представление: одночлен — вектор показателей, храним только ненулевые члены.
//
// Прежняя версия была вложенной по уровням и жёстко знала про три переменные
// (level === 3 — базовый случай). Такое представление ломается ровно там, где
// нам теперь нужно: число образующих меняется по ходу построения (дорисовали
// точку — появилась переменная), а при вложенности это меняет глубину, то есть
// все уже посчитанные многочлены пришлось бы перестраивать. В плоском виде
// отсутствующая переменная — просто нулевой показатель, и старые выражения
// остаются валидными как есть.
//
// Ключ одночлена — показатели через запятую с обрезанными хвостовыми нулями,
// поэтому a·b даёт "1,1" и в кольце из трёх образующих, и из десяти.

// Строится на каждое произведение членов, поэтому собираем строку напрямую,
// без промежуточного среза массива.
// Ключ одночлена — ЧИСЛО, когда показатели в него укладываются, и строка иначе.
//
// Раньше ключ всегда был склейкой строк, и на каждый член каждого произведения
// приходилась новая строка. Профиль показывал треть времени в сборке
// одночленов, но настоящая цена выше: горы мусора давят на сборщик, а во
// вкладке браузера, где память делится с апплетом GeoGebra, это бьёт куда
// больнее, чем в отдельном процессе.
//
// Упаковка: по шесть бит на показатель, до восьми образующих — ровно умещается
// в точные целые double. Ведущая единица обязательна, иначе одночлены [1] и
// [0,1] дали бы один ключ. Что не влезает (девятая буква, степень выше 63) —
// уходит на строковый путь: медленнее, но верно.
//
// ВАЖНО: это ЕДИНСТВЕННОЕ место, где строится ключ. Первая попытка перейти на
// числа провалилась именно потому, что мест было два — `addProduct` считал
// ключ по-своему, и один и тот же одночлен получал разные ключи, множился в
// двух записях, а многочлен становился неверным молча. Второй реализации здесь
// быть не должно никогда.
const KEY_BASE = 64;
const KEY_MAX_DEG = 63;
const KEY_MAX_VARS = 8;

function keyFor(exp, end) {
  if (end === 0) return 0;
  if (end <= KEY_MAX_VARS) {
    let k = 1;
    let i = 0;
    for (; i < end; i++) {
      const e = exp[i];
      if (e > KEY_MAX_DEG) break;
      k = k * KEY_BASE + e;
    }
    if (i === end) return k;
  }
  let key = String(exp[0]);
  for (let i = 1; i < end; i++) key += ',' + exp[i];
  return key;
}

const EMPTY_KEY = keyFor([], 0);

function expKey(exp) {
  let end = exp.length;
  while (end > 0 && exp[end - 1] === 0) end--;
  return keyFor(exp, end);
}

function normExp(exp) {
  let end = exp.length;
  while (end > 0 && exp[end - 1] === 0) end--;
  return exp.slice(0, end);
}

export class Poly {
  // entries: Map<key, {exp, coeff}>; коэффициент никогда не нулевой
  constructor(entries = new Map()) { this.entries = entries; }

  get size() { return this.entries.size; }
  isZero() { return this.entries.size === 0; }
  terms() { return [...this.entries.values()]; }
}

export function zero() { return new Poly(); }

export function constant(value) {
  const c = value instanceof CFrac ? value : CFrac.from(value);
  if (c.isZero()) return zero();
  return new Poly(new Map([[EMPTY_KEY, { exp: [], coeff: c }]]));
}

const variableCache = [];

export function variable(index) {
  if (variableCache[index]) return variableCache[index];
  const exp = new Array(index + 1).fill(0);
  exp[index] = 1;
  // Одночлены-переменные неизменяемы и запрашиваются постоянно (возведение в
  // степень, деление, подстановка) — держим по одному экземпляру.
  return (variableCache[index] = new Poly(new Map([[expKey(exp), { exp: normExp(exp), coeff: ONE }]])));
}

// Записи в собираемой карте всегда свежие, поэтому коэффициент можно менять
// на месте, а не пересоздавать объект.
function bump(map, key, cur, coeff) {
  const sum = cur.coeff.add(coeff);
  if (sum.isZero()) map.delete(key);
  else cur.coeff = sum;
}

function addTermInto(map, exp, coeff) {
  if (coeff.isZero()) return;
  let end = exp.length;
  while (end > 0 && exp[end - 1] === 0) end--;
  const key = keyOf(exp, end);
  const cur = map.get(key);
  // Показатели неизменяемы по всему движку (кто их меняет — сначала копирует),
  // поэтому уже обрезанный массив можно переиспользовать, а не клонировать.
  if (!cur) map.set(key, { exp: end === exp.length ? exp : exp.slice(0, end), coeff });
  else bump(map, key, cur, coeff);
}

// Тот же ключ, только длина уже известна вызывающему. ОБЯЗАН совпадать с
// expKey: если один и тот же одночлен получит числовой ключ по одному пути и
// строковый по другому, он размножится в двух записях, и многочлен станет
// неверным молча.
const keyOf = keyFor;

export function add(x, y) {
  // Проверка бюджета во ВСЕХ петлях по членам, а не в избранных: искать
  // непокрытый путь по одному оказалось делом на несколько дней.
  checkIfHeavy(x.size + y.size);
  const out = new Map();
  for (const { exp, coeff } of x.entries.values()) addTermInto(out, exp, coeff);
  for (const { exp, coeff } of y.entries.values()) addTermInto(out, exp, coeff);
  return new Poly(out);
}

export function neg(x) {
  checkIfHeavy(x.size);
  const out = new Map();
  for (const [k, { exp, coeff }] of x.entries) out.set(k, { exp, coeff: coeff.neg() });
  return new Poly(out);
}

export function sub(x, y) { return add(x, neg(y)); }

// Умножение — самая горячая операция, и раньше на КАЖДУЮ пару членов
// создавался массив показателей, даже если такой одночлен уже встречался.
// Теперь ключ собирается сразу из двух векторов, а массив создаётся только для
// действительно нового одночлена. Это и была основная нагрузка на сборщик мусора.
function addProduct(map, ea, eb, coeff) {
  // Ключ обязан считаться ТОЙ ЖЕ функцией, что и везде. Раньше здесь была своя
  // склейка строк, и она вдобавок не обрезала хвостовые нули: пока ключи всюду
  // были строками, это сходилось само собой, а стоило перейти на числовые — и
  // один и тот же одночлен стал получать два разных ключа. Многочлен от такого
  // ломается молча, поэтому никакой второй реализации ключа быть не должно.
  let n = ea.length > eb.length ? ea.length : eb.length;
  while (n > 0 && ((ea[n - 1] ?? 0) + (eb[n - 1] ?? 0)) === 0) n--;

  const exp = new Array(n);
  for (let i = 0; i < n; i++) exp[i] = (ea[i] ?? 0) + (eb[i] ?? 0);

  const key = keyFor(exp, n);
  const cur = map.get(key);
  if (cur) { bump(map, key, cur, coeff); return; }
  map.set(key, { exp, coeff });
}

export function mul(x, y) {
  // Одно умножение больших многочленов — миллионы операций и десятки секунд.
  // Без проверки ЗДЕСЬ бюджет опаздывал на минуту: следующий вызов НОДа, где
  // он проверялся, случался уже после.
  checkIfHeavy(x.size * y.size);
  const out = new Map();
  for (const tx of x.entries.values()) {
    for (const ty of y.entries.values()) {
      const coeff = tx.coeff.mul(ty.coeff);
      if (!coeff.isZero()) addProduct(out, tx.exp, ty.exp, coeff);
    }
  }
  return new Poly(out);
}

export function scale(x, factor) {
  checkIfHeavy(x.size);
  const f = factor instanceof CFrac ? factor : CFrac.from(factor);
  if (f.isZero()) return zero();
  const out = new Map();
  for (const [k, { exp, coeff }] of x.entries) out.set(k, { exp, coeff: coeff.mul(f) });
  return new Poly(out);
}

export function pow(x, n) {
  let acc = constant(ONE);
  for (let i = 0; i < n; i++) acc = mul(acc, x);
  return acc;
}

export function equals(x, y) { return sub(x, y).isZero(); }

export function isOne(x) {
  if (x.entries.size !== 1) return false;
  // Ключ пустого одночлена берётся у той же функции, что строит все остальные:
  // зашивать его строкой нельзя — он перестал быть строкой.
  const t = x.entries.get(EMPTY_KEY);
  return !!t && t.coeff.isOne();
}

export function evalPoly(poly, values) {
  checkIfHeavy(poly.size);
  let acc = ZERO;
  for (const { exp, coeff } of poly.entries.values()) {
    let term = coeff;
    for (let v = 0; v < exp.length; v++) {
      for (let p = 0; p < exp[v]; p++) term = term.mul(values[v]);
    }
    acc = acc.add(term);
  }
  return acc;
}

// То же самое, но в обычных числах с плавающей точкой: values — массив
// { re, im }. Нужно для сверки с настоящим чертежом (см. geogebra/numeric.js).
export function evalPolyFloat(poly, values) {
  let accRe = 0, accIm = 0;
  for (const { exp, coeff } of poly.entries.values()) {
    let re = coeff.re.toNumber(), im = coeff.im.toNumber();
    for (let v = 0; v < exp.length; v++) {
      const val = values[v];
      for (let p = 0; p < exp[v]; p++) {
        const nre = re * val.re - im * val.im;
        im = re * val.im + im * val.re;
        re = nre;
      }
    }
    accRe += re;
    accIm += im;
  }
  return { re: accRe, im: accIm };
}

export function terms(poly) { return poly.terms(); }

export function fromTerms(termList) {
  const out = new Map();
  for (const { exp, coeff } of termList) addTermInto(out, exp, coeff);
  return new Poly(out);
}

// Наибольшая степень переменной index в многочлене.
export function degreeIn(poly, index) {
  let d = 0;
  for (const { exp } of poly.entries.values()) d = Math.max(d, exp[index] ?? 0);
  return d;
}

export function involvesVar(poly, index) { return degreeIn(poly, index) > 0; }

// Взгляд на многочлен как на многочлен от ОДНОЙ переменной index:
// возвращает массив коэффициентов (сами многочлены без этой переменной).
export function coeffsIn(poly, index) {
  checkIfHeavy(poly.size);
  const out = [];
  for (const { exp, coeff } of poly.entries.values()) {
    const e = exp[index] ?? 0;
    const rest = exp.slice();
    if (index < rest.length) rest[index] = 0;
    while (out.length <= e) out.push(new Map());
    addTermInto(out[e], rest, coeff);
  }
  return out.map(m => new Poly(m));
}

// ---- деление на линейный множитель --------------------------------------
// Делит poly на (x_index − root), где root не содержит x_index. Схема Горнера
// по коэффициентам при степенях x_index; «взгляд как на одномерный многочлен»
// строится на лету через coeffsIn.
export function divideByLinearFactor(poly, index, root) {
  checkIfHeavy(poly.size);
  const c = coeffsIn(poly, index);
  const n = c.length - 1;
  if (n < 0) return { quotient: zero(), remainder: zero(), ok: true };

  const q = new Array(Math.max(n, 0)).fill(null).map(() => zero());
  let carry = c[n];
  for (let i = n - 1; i >= 0; i--) {
    q[i] = carry;
    carry = add(c[i], mul(root, carry));
  }
  let quotient = zero();
  const x = variable(index);
  for (let k = 0; k < q.length; k++) quotient = add(quotient, mul(q[k], pow(x, k)));
  return { quotient, remainder: carry, ok: carry.isZero() };
}

// ---- канонический порядок и нормировка ----------------------------------

// Полная степень по убыванию, затем показатели по переменным по убыванию.
export function compareExp(x, y) {
  let dx = 0, dy = 0;
  for (const e of x) dx += e;
  for (const e of y) dy += e;
  if (dx !== dy) return dy - dx;
  const n = Math.max(x.length, y.length);
  for (let v = 0; v < n; v++) {
    const a = x[v] ?? 0, b = y[v] ?? 0;
    if (a !== b) return b - a;
  }
  return 0;
}

export function leadingCoeff(poly) {
  let best = null;
  for (const t of poly.entries.values()) {
    if (best === null || compareExp(t.exp, best.exp) < 0) best = t;
  }
  return best === null ? null : best.coeff;
}

function bigAbs(x) { return x < 0n ? -x : x; }
function bigGcd(a, b) {
  a = bigAbs(a); b = bigAbs(b);
  while (b) { [a, b] = [b, a % b]; }
  return a;
}
function bigLcm(a, b) { return a === 0n || b === 0n ? 0n : bigAbs(a * b) / bigGcd(a, b); }

// НОК знаменателей всех коэффициентов — на него домножают, чтобы вычистить
// дроби из коэффициентов.
export function coeffDenomLcm(poly) {
  let l = 1n;
  for (const { coeff } of poly.entries.values()) {
    l = bigLcm(l, coeff.re.d);
    l = bigLcm(l, coeff.im.d);
  }
  return l;
}

// НОД целых числителей всех коэффициентов; 0n для нулевого многочлена.
export function coeffNumGcd(poly) {
  let g = 0n;
  for (const { coeff } of poly.entries.values()) {
    g = bigGcd(g, coeff.re.n);
    g = bigGcd(g, coeff.im.n);
  }
  return g;
}

export { bigGcd, bigLcm };
