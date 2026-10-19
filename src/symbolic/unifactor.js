// Разложение ОДНОМЕРНОГО многочлена на неприводимые над конечным полем.
//
// Это дно будущего полного разложения: многомерное сводится подстановкой к
// одномерному, а поднимается обратно по Гензелю. Само по себе оно тоже нужно —
// без него нельзя ни доказать неприводимость, ни разбить множитель, у которого
// нет линейных делителей.
//
// Схема классическая и делится на три независимых шага:
//
//   1) БЕСКВАДРАТНОЕ разложение — отделить кратности. Держится на том, что у
//      кратного множителя тот же множитель есть и у производной, поэтому
//      НОД(f, f′) ловит ровно кратные части. В нашем поле характеристика
//      огромна (простое около 33 миллионов), а степени — десятки, поэтому
//      вырождений вида «производная равна нулю» здесь не бывает;
//   2) разложение ПО СТЕПЕНЯМ (distinct-degree) — собрать вместе все
//      неприводимые множители одинаковой степени d. Держится на том, что
//      x^(q^d) − x есть произведение ВСЕХ неприводимых, чьи степени делят d:
//      элементы поля из q^d элементов — это в точности корни этого многочлена;
//   3) разделение РАВНЫХ степеней (Кантор–Цассенхаус) — разбить произведение
//      неприводимых одной степени. Здесь без случайности не обойтись: берём
//      случайный многочлен, возводим в степень (q^d − 1)/2 и смотрим НОД с
//      исходным. У половины элементов поля это даёт нетривиальный делитель,
//      поэтому несколько попыток разделяют почти наверняка.
//
// Проверять ответ не нужно так, как проверяется НОД: здесь произведение
// множителей сходится с исходным по построению, и тест это подтверждает.

import { checkComputeBudget } from './budget.js';
import { trimArr, subArray, arrayOps } from './modpoly.js';

// Арифметика массивов специализируется по полю (см. modpoly.js), поэтому берём
// её один раз на поле, а не на каждый вызов.
const opsCache = new WeakMap();
function ops(F) {
  let value = opsCache.get(F);
  if (!value) { value = arrayOps(F); opsCache.set(F, value); }
  return value;
}


// ---- мелочь ----------------------------------------------------------------

const xPoly = F => [0, F.one];

function monicOf(F, a) {
  if (a.length === 0) return a;
  const lead = a[a.length - 1];
  if (lead === F.one) return a.slice();
  const inv = F.inv(lead);
  return a.map(c => F.mul(c, inv));
}

// Производная. Множитель — целое i, поэтому переводим его в поле.
function derivative(F, a) {
  if (a.length <= 1) return [];
  const out = new Array(a.length - 1);
  for (let i = 1; i < a.length; i++) out[i - 1] = F.mul(a[i], F.of(i));
  return trimArr(out);
}

function mulMod(F, a, b, mod) { return ops(F).remArray(ops(F).mulArray(a, b), mod); }

// Возведение в степень по модулю многочлена. Показатель — bigint: в нём легко
// набирается пара сотен бит (q^d при q около 10^15), а вот коэффициенты всё
// это время остаются машинными.
function powMod(F, base, exp, mod) {
  let result = [F.one];
  let b = ops(F).remArray(base, mod);
  let e = exp;
  while (e > 0n) {
    checkComputeBudget();
    if (e & 1n) result = mulMod(F, result, b, mod);
    e >>= 1n;
    if (e > 0n) b = mulMod(F, b, b, mod);
  }
  return result;
}

function randomPoly(F, degreeBelow, rnd) {
  const out = new Array(degreeBelow);
  for (let i = 0; i < degreeBelow; i++) out[i] = F.of(rnd(F.p), rnd(F.p));
  return trimArr(out);
}

// ---- шаг 1: бесквадратное разложение ---------------------------------------

// Возвращает пары «множитель, кратность»: множители попарно взаимно просты и
// сами свободны от квадратов.
export function squarefreeParts(F, f) {
  const out = [];
  const d = derivative(F, f);
  if (d.length === 0) return [{ poly: f, power: 1 }];

  let c = ops(F).gcdArray(f, d);        // всё, что входит с кратностью выше первой
  let w = ops(F).divideArray(f, c);     // по одному экземпляру каждого множителя
  if (!w) return null;
  let power = 1;
  while (w.length > 1) {
    checkComputeBudget();
    const y = ops(F).gcdArray(w, c);    // то, что входит с кратностью выше текущей
    const z = ops(F).divideArray(w, y); // а это — ровно с текущей
    if (!z) return null;
    if (z.length > 1) out.push({ poly: z, power });
    w = y;
    const next = ops(F).divideArray(c, y);
    if (!next) return null;
    c = next;
    power++;
  }
  return out;
}

// ---- шаг 2: разложение по степеням -----------------------------------------

// Разбивает бесквадратный многочлен на куски, каждый из которых — произведение
// неприводимых ОДНОЙ степени.
function distinctDegree(F, f, q) {
  const out = [];
  const x = xPoly(F);
  let v = f;
  let h = x;
  let d = 0;
  while (v.length - 1 >= 2 * (d + 1)) {
    checkComputeBudget();
    d++;
    h = powMod(F, h, q, v);                    // h = x^(q^d) mod v
    const g = ops(F).gcdArray(subArray(F, h, x), v);
    if (g.length > 1) {
      out.push({ poly: g, degree: d });
      const rest = ops(F).divideArray(v, g);
      if (!rest) return null;
      v = rest;
      h = ops(F).remArray(h, v);
    }
  }
  // Что осталось — неприводимо: множителей меньшей степени в нём уже нет.
  if (v.length > 1) out.push({ poly: v, degree: v.length - 1 });
  return out;
}

// ---- шаг 3: разделение равных степеней -------------------------------------

const SPLIT_ATTEMPTS = 64;

function equalDegree(F, f, d, q, rnd) {
  const factors = [];
  const stack = [f];
  while (stack.length > 0) {
    const g = stack.pop();
    const n = g.length - 1;
    if (n === d) { factors.push(g); continue; }

    let split = null;
    const exp = (q ** BigInt(d) - 1n) / 2n;
    for (let attempt = 0; attempt < SPLIT_ATTEMPTS && !split; attempt++) {
      checkComputeBudget();
      const a = randomPoly(F, n, rnd);
      if (a.length <= 1) continue;

      // Иногда везёт сразу: случайный многочлен имеет с g общий множитель.
      let t = ops(F).gcdArray(a, g);
      if (t.length > 1 && t.length - 1 < n) { split = t; break; }

      // Основной ход: a^((q^d−1)/2) − 1. У половины элементов поля это даёт
      // нетривиальный НОД, поэтому попыток нужно немного.
      const b = powMod(F, a, exp, g);
      t = ops(F).gcdArray(subArray(F, b, [F.one]), g);
      if (t.length > 1 && t.length - 1 < n) split = t;
    }
    if (!split) return null;                   // не разделилось — редкость

    const other = ops(F).divideArray(g, split);
    if (!other) return null;
    stack.push(split, other);
  }
  return factors;
}

// ---- вход ------------------------------------------------------------------

// Полное разложение на неприводимые. Возвращает список «множитель, кратность»
// (множители монические) или null, если разделить не удалось.
//
// Старший коэффициент исходного многочлена сюда не входит: множители
// монические, а константу вызывающий держит отдельно.
export function factorUnivariate(F, poly, rnd) {
  const f = monicOf(F, trimArr(poly.slice()));
  if (f.length <= 1) return [];
  if (f.length === 2) return [{ poly: f, power: 1 }];      // линейный

  const q = BigInt(F.p) * BigInt(F.p);
  const parts = squarefreeParts(F, f);
  if (!parts) return null;

  const out = [];
  for (const { poly: part, power } of parts) {
    const chunks = distinctDegree(F, part, q);
    if (!chunks) return null;
    for (const { poly: chunk, degree } of chunks) {
      const pieces = equalDegree(F, chunk, degree, q, rnd);
      if (!pieces) return null;
      for (const piece of pieces) out.push({ poly: monicOf(F, piece), power });
    }
  }
  return out;
}
