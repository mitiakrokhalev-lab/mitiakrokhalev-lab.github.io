// Полное разложение МНОГОМЕРНОГО многочлена на неприводимые — по требованию.
//
// Третий, последний этап. Первые два умеют раскладывать одномерный многочлен:
// по модулю простого (unifactor.js) и над гауссовыми целыми (zfactor.js).
// Здесь многомерный сводится к одномерному подстановкой, а ответ поднимается
// обратно.
//
// Схема:
//
//   1) выбрать ГЛАВНУЮ переменную и подставить числа вместо остальных так,
//      чтобы степень по главной не упала, а образ остался свободным от
//      квадратов;
//   2) разложить одномерный образ над Z[i];
//   3) ПОДНЯТЬ разложение обратно: по модулю идеала (x−α) множители известны,
//      каждый шаг уточняет их на один порядок по остальным переменным;
//   4) собрать настоящие множители перебором подмножеств, годность решает
//      точное деление.
//
// Главная хитрость — в подготовке. У многомерного многочлена старший
// коэффициент по главной переменной сам является многочленом, и подъём с ним
// требует отдельной поправки (у Ванга это самая тонкая часть всей теории).
// Поэтому мы сначала делаем многочлен МОНИЧЕСКИМ заменой x ↦ x/ℓ с домножением
// на ℓ^(n−1): у монического старший коэффициент — единица, и поправка не нужна
// вовсе. Обратная замена в конце возвращает настоящие множители, а проверка
// делением всё равно стоит последней, поэтому ошибиться нельзя.
//
// Это разложение НЕ зовётся при отрисовке: там работает дешёвое и неполное
// (см. gcd.js). Здесь цена не ограничена — сюда приходят по явной просьбе.

import * as P from './poly.js';
import { CFrac, ONE, ZERO } from './complex-fraction.js';
import { Fraction } from './fraction.js';
import { checkComputeBudget } from './budget.js';
import { polyGcd, divideExact, primitivePart, contentAndPrimitive } from './gcd.js';
import { factorSquarefreeOverZi } from './zfactor.js';

// ---- одномерные многочлены как массивы над Q(i) ----------------------------

const uniTrim = a => { while (a.length > 0 && a[a.length - 1].isZero()) a.pop(); return a; };

function uniMul(a, b) {
  if (a.length === 0 || b.length === 0) return [];
  const out = new Array(a.length + b.length - 1).fill(ZERO);
  for (let i = 0; i < a.length; i++) {
    if (a[i].isZero()) continue;
    for (let j = 0; j < b.length; j++) {
      if (b[j].isZero()) continue;
      out[i + j] = out[i + j].add(a[i].mul(b[j]));
    }
  }
  return uniTrim(out);
}

function uniSub(a, b) {
  const out = new Array(Math.max(a.length, b.length));
  for (let i = 0; i < out.length; i++) out[i] = (a[i] ?? ZERO).sub(b[i] ?? ZERO);
  return uniTrim(out);
}

// Деление с остатком над полем.
function uniDivMod(a, b) {
  const db = b.length - 1;
  const inv = ONE.div(b[db]);
  const rem = a.slice();
  const quot = new Array(Math.max(0, a.length - db)).fill(ZERO);
  for (let k = rem.length - 1; k >= db; k--) {
    if (rem[k].isZero()) continue;
    const factor = rem[k].mul(inv);
    quot[k - db] = factor;
    for (let i = 0; i <= db; i++) rem[k - db + i] = rem[k - db + i].sub(factor.mul(b[i]));
  }
  return { quot: uniTrim(quot), rem: uniTrim(rem) };
}

// s·g + t·h = 1. Существует ровно потому, что образ свободен от квадратов, а
// значит его множители попарно взаимно просты.
function uniBezout(g, h) {
  let [r0, r1] = [g.slice(), h.slice()];
  let [s0, s1] = [[ONE], []];
  let [t0, t1] = [[], [ONE]];
  while (r1.length > 0) {
    const { quot, rem } = uniDivMod(r0, r1);
    [r0, r1] = [r1, rem];
    [s0, s1] = [s1, uniSub(s0, uniMul(quot, s1))];
    [t0, t1] = [t1, uniSub(t0, uniMul(quot, t1))];
  }
  if (r0.length !== 1) return null;                    // не взаимно просты
  const inv = ONE.div(r0[0]);
  return { s: s0.map(c => c.mul(inv)), t: t0.map(c => c.mul(inv)) };
}

// ---- перевод между Poly и массивами ----------------------------------------

function toUni(poly, v) {
  const parts = P.coeffsIn(poly, v);
  return uniTrim(parts.map(part => (part.isZero() ? ZERO : P.leadingCoeff(part))));
}

function fromUni(arr, v) {
  const terms = [];
  for (let e = 0; e < arr.length; e++) {
    if (arr[e].isZero()) continue;
    const exp = new Array(v + 1).fill(0);
    exp[v] = e;
    terms.push({ exp, coeff: arr[e] });
  }
  return P.fromTerms(terms);
}

// Гауссовы целые для zfactor: он работает с парами bigint-ов.
function toGzArray(arr) {
  return arr.map(c => {
    if (c.re.d !== 1n || c.im.d !== 1n) return null;
    return { re: c.re.n, im: c.im.n };
  });
}

const fromGzArray = arr =>
  arr.map(c => new CFrac(new Fraction(c.re, 1n), new Fraction(c.im, 1n)));

// ---- подготовка ------------------------------------------------------------

// Подстановка x_j ↦ x_j + a: схема Горнера по коэффициентам при степенях x_j.
function shiftVar(poly, j, a) {
  if (a.isZero()) return poly;
  const parts = P.coeffsIn(poly, j);
  const xa = P.add(P.variable(j), P.constant(a));
  let acc = P.zero();
  for (let e = parts.length - 1; e >= 0; e--) acc = P.add(P.mul(acc, xa), parts[e]);
  return acc;
}

// Однородная часть степени k по переменным, отличным от главной.
function homogeneousPart(poly, v, k) {
  const terms = [];
  for (const { exp, coeff } of P.terms(poly)) {
    let degree = 0;
    for (let j = 0; j < exp.length; j++) if (j !== v) degree += exp[j];
    if (degree === k) terms.push({ exp, coeff });
  }
  return P.fromTerms(terms);
}

// Полная степень по всем переменным, кроме главной.
function otherDegree(poly, v) {
  let best = 0;
  for (const { exp } of P.terms(poly)) {
    let degree = 0;
    for (let j = 0; j < exp.length; j++) if (j !== v) degree += exp[j];
    if (degree > best) best = degree;
  }
  return best;
}

function varsOf(poly) {
  const out = [];
  let top = 0;
  for (const { exp } of P.terms(poly)) top = Math.max(top, exp.length);
  for (let v = 0; v < top; v++) if (P.degreeIn(poly, v) > 0) out.push(v);
  return out;
}

// ---- подъём по идеалу ------------------------------------------------------

// Отбрасывание членов выше нужной степени по остальным переменным. Подъём идёт
// «по модулю идеала в степени k», и всё, что выше, к делу не относится.
function truncate(poly, v, bound) {
  const terms = [];
  for (const { exp, coeff } of P.terms(poly)) {
    let degree = 0;
    for (let j = 0; j < exp.length; j++) if (j !== v) degree += exp[j];
    if (degree <= bound) terms.push({ exp, coeff });
  }
  return P.fromTerms(terms);
}

// Поднимает разложение f ≡ g·h (по модулю «все остальные переменные равны
// нулю») до нужной точности. Оба множителя МОНИЧЕСКИЕ по главной переменной,
// поэтому поправка старшего коэффициента не нужна.
function liftPair(f, g, h, v, bound) {
  const g0 = toUni(homogeneousPart(g, v, 0), v);
  const h0 = toUni(homogeneousPart(h, v, 0), v);
  const bez = uniBezout(g0, h0);
  if (!bez) return null;

  let G = g, H = h;
  for (let k = 1; k <= bound; k++) {
    checkComputeBudget();
    const error = truncate(P.sub(f, P.mul(G, H)), v, bound);
    if (error.isZero()) break;
    const piece = homogeneousPart(error, v, k);
    if (piece.isZero()) continue;

    // Уравнение δg·h₀ + δh·g₀ = piece решается для КАЖДОГО одночлена от
    // остальных переменных отдельно: по главной переменной это обычное
    // одномерное диофантово уравнение.
    const byMonomial = new Map();
    for (const { exp, coeff } of P.terms(piece)) {
      const rest = exp.slice();
      const e = rest[v] ?? 0;
      if (v < rest.length) rest[v] = 0;
      const key = rest.join(',');
      let entry = byMonomial.get(key);
      if (!entry) { entry = { exp: rest, coeffs: [] }; byMonomial.set(key, entry); }
      while (entry.coeffs.length <= e) entry.coeffs.push(ZERO);
      entry.coeffs[e] = entry.coeffs[e].add(coeff);
    }

    let dG = P.zero(), dH = P.zero();
    for (const { exp, coeffs } of byMonomial.values()) {
      const c = uniTrim(coeffs);
      if (c.length === 0) continue;
      const { quot, rem } = uniDivMod(uniMul(c, bez.t), g0);
      const deltaG = rem;
      const deltaH = uniSub(uniMul(c, bez.s), uniMul(quot, h0).map(x => x.neg()));
      const monomial = P.fromTerms([{ exp, coeff: ONE }]);
      dG = P.add(dG, P.mul(fromUni(deltaG, v), monomial));
      dH = P.add(dH, P.mul(fromUni(deltaH, v), monomial));
    }
    G = P.add(G, dG);
    H = P.add(H, dH);
  }

  // Точного равенства не требуем: если исходный многочлен неприводим, а его
  // образ распался, произведение сойдётся только до нужной степени. Настоящий
  // ответ соберёт перебор подмножеств, а решит его точное деление.
  return { G: truncate(G, v, bound), H: truncate(H, v, bound) };
}

// Поднимает весь список: делим пополам, поднимаем пару, рекурсия.
function liftAll(f, factors, v, bound) {
  if (factors.length === 1) return [f];
  const half = Math.ceil(factors.length / 2);
  const left = factors.slice(0, half), right = factors.slice(half);
  const g0 = left.reduce((acc, x) => uniMul(acc, x), [ONE]);
  const h0 = right.reduce((acc, x) => uniMul(acc, x), [ONE]);

  const lifted = liftPair(f, fromUni(g0, v), fromUni(h0, v), v, bound);
  if (!lifted) return null;

  const leftParts = liftAll(lifted.G, left, v, bound);
  const rightParts = liftAll(lifted.H, right, v, bound);
  if (!leftParts || !rightParts) return null;
  return [...leftParts, ...rightParts];
}

// Монизация: x ↦ x/ℓ с домножением на ℓ^(n−1). Коэффициент при x^i получает
// множитель ℓ^(n−1−i), а старший обращается ровно в единицу — ℓ сокращается сам.
function monicize(poly, v, lead) {
  const parts = P.coeffsIn(poly, v);
  const n = parts.length - 1;
  const powers = [P.constant(ONE)];
  for (let k = 1; k <= n - 1; k++) powers.push(P.mul(powers[k - 1], lead));
  let out = P.pow(P.variable(v), n);
  for (let i = 0; i < n; i++) {
    if (parts[i].isZero()) continue;
    out = P.add(out, P.mul(P.mul(parts[i], powers[n - 1 - i]), P.pow(P.variable(v), i)));
  }
  return out;
}

// Примитивная часть по переменной: снимаем МНОГОЧЛЕННОЕ содержимое.
//
// Нужна ровно после обратной замены: множитель (a + bc) при подстановке
// a ↦ b²a превращается в b²a + bc = b·(ab + c), и лишнее b обязано уйти —
// иначе кандидат не поделит исходный многочлен, и разложение сорвётся на
// ровном месте. Поймал это тест «ни по одной переменной старший коэффициент
// не число».
function primitiveInVar(poly, v) {
  const parts = P.coeffsIn(poly, v).filter(part => !part.isZero());
  if (parts.length === 0) return poly;
  let g = parts[0];
  for (let i = 1; i < parts.length && !P.isOne(g); i++) g = polyGcd(g, parts[i]);
  if (P.isOne(g)) return poly;
  return divideExact(poly, g) ?? poly;
}

// Обратная замена x ↦ ℓ·x.
function unmonicize(poly, v, lead) {
  const parts = P.coeffsIn(poly, v);
  let out = P.zero();
  for (let i = 0; i < parts.length; i++) {
    if (parts[i].isZero()) continue;
    out = P.add(out, P.mul(P.mul(parts[i], P.pow(lead, i)), P.pow(P.variable(v), i)));
  }
  return out;
}

// ---- вход ------------------------------------------------------------------

const POINT_ATTEMPTS = 30;

// Раскладывает БЕСКВАДРАТНЫЙ примитивный многочлен. Возвращает список
// неприводимых множителей или null, если не получилось (тогда вызывающий
// оставляет многочлен как есть).
export function factorSquarefree(poly, rnd) {
  const vars = varsOf(poly);
  if (vars.length === 0) return [];
  if (vars.length === 1) {
    const arr = toGzArray(toUni(poly, vars[0]));
    if (arr.some(c => c === null)) return null;
    const parts = factorSquarefreeOverZi(arr, rnd);
    if (!parts) return null;
    return parts.map(part => fromUni(fromGzArray(part), vars[0]));
  }

  // Главная переменная: та, у которой старший коэффициент — просто число.
  // Тогда монизация не нужна вовсе; иначе берём переменную наибольшей степени.
  let main = vars[0];
  for (const v of vars) {
    const lead = P.coeffsIn(poly, v)[P.degreeIn(poly, v)];
    if (lead.size === 1 && P.terms(lead)[0].exp.every(e => e === 0)) { main = v; break; }
    if (P.degreeIn(poly, v) > P.degreeIn(poly, main)) main = v;
  }

  const leadPoly = P.coeffsIn(poly, main)[P.degreeIn(poly, main)];
  const monicByNature = leadPoly.size === 1 && P.terms(leadPoly)[0].exp.every(e => e === 0);
  const others = vars.filter(v => v !== main);

  // Если старший коэффициент — многочлен, делаем замену x ↦ x/ℓ с домножением
  // на ℓ^(n−1). Получается МОНИЧЕСКИЙ многочлен, и вся возня со старшим
  // коэффициентом при подъёме исчезает: у монического он единица. Обратная
  // замена в конце возвращает настоящие множители, а проверку делением всё
  // равно проходит каждый кандидат, так что подмена ничего не портит.
  const normalized = monicByNature
    ? (P.terms(leadPoly)[0].coeff.isOne()
      ? poly : P.scale(poly, ONE.div(P.terms(leadPoly)[0].coeff)))
    : monicize(poly, main, leadPoly);
  const backSubstitute = monicByNature ? null : leadPoly;

  for (let attempt = 0; attempt < POINT_ATTEMPTS; attempt++) {
    checkComputeBudget();
    // Точка подстановки: маленькие числа, потому что коэффициенты образа растут
    // как их степени.
    const point = new Map();
    for (const v of others) point.set(v, new CFrac(BigInt(rnd(9) - 4)));

    let image = normalized;
    for (const [v, value] of point) image = evalAt(image, v, value);
    if (P.degreeIn(image, main) !== P.degreeIn(normalized, main)) continue;

    // Образ обязан быть свободен от квадратов: иначе множители по модулю
    // идеала не взаимно просты, и подъём не определён.
    const derivative = derivativeIn(image, main);
    if (derivative.isZero()) continue;
    if (P.degreeIn(polyGcd(image, derivative), main) > 0) continue;

    const arr = toGzArray(toUni(image, main));
    if (arr.some(c => c === null)) continue;
    const modular = factorSquarefreeOverZi(arr, rnd);
    if (!modular) continue;
    if (modular.length === 1) return [poly];            // образ неприводим ⟹ и сам

    // Сдвигаем точку в ноль: тогда «по модулю идеала» — это просто «члены без
    // остальных переменных», и однородные части выделяются одним фильтром.
    let shifted = normalized;
    for (const [v, value] of point) shifted = shiftVar(shifted, v, value);

    const bound = otherDegree(shifted, main);
    const lifted = liftAll(shifted, modular.map(fromGzArray), main, bound);
    if (!lifted) continue;

    const result = recombine(lifted, poly, point, main, bound, backSubstitute);
    if (result) return result;
  }
  return null;
}

// Сборка настоящих множителей из поднятых кусков.
//
// Брать каждый кусок по отдельности НЕЛЬЗЯ: подстановка может расщепить
// многочлен сильнее, чем он раскладывается на самом деле. Простейший пример —
// `a² − b`: он неприводим, а при b = 4 образ равен (a−2)(a+2). Поэтому
// перебираются ПОДМНОЖЕСТВА, а годность решает точное деление: неверная
// комбинация просто не поделит.
function recombine(pieces, poly, point, v, bound, backSubstitute) {
  const used = new Array(pieces.length).fill(false);
  const out = [];
  let rest = poly;

  for (let size = 1; size <= pieces.length; size++) {
    let again = true;
    while (again) {
      again = false;
      const chosen = [];
      const walk = (start, left) => {
        if (again) return;
        if (left === 0) {
          checkComputeBudget();
          let product = P.constant(ONE);
          for (const i of chosen) product = truncate(P.mul(product, pieces[i]), v, bound);
          let candidate = product;
          for (const [j, value] of point) candidate = shiftVar(candidate, j, value.neg());
          // Если многочлен монизировали, кандидат живёт в подменённых
          // координатах: возвращаем замену x ↦ ℓ·x и снимаем содержимое.
          if (backSubstitute) candidate = unmonicize(candidate, v, backSubstitute);
          candidate = primitivePart(primitiveInVar(candidate, v));
          if (P.isOne(candidate)) return;
          const quotient = divideExact(rest, candidate);
          if (quotient) {
            out.push(candidate);
            rest = quotient;
            for (const i of chosen) used[i] = true;
            again = true;
          }
          return;
        }
        for (let i = start; i < pieces.length; i++) {
          if (used[i]) continue;
          chosen.push(i);
          walk(i + 1, left - 1);
          chosen.pop();
          if (again) return;
        }
      };
      walk(0, size);
    }
  }

  if (!rest.isZero() && !P.isOne(rest) && rest.size > 1) out.push(primitivePart(rest));
  return out.length > 0 ? out : null;
}

// Значение по одной переменной.
function evalAt(poly, v, value) {
  const parts = P.coeffsIn(poly, v);
  let acc = P.zero();
  for (let e = parts.length - 1; e >= 0; e--) acc = P.add(P.scale(acc, value), parts[e]);
  return acc;
}

function derivativeIn(poly, v) {
  const terms = [];
  for (const { exp, coeff } of P.terms(poly)) {
    const e = exp[v] ?? 0;
    if (e === 0) continue;
    const next = exp.slice();
    next[v] = e - 1;
    terms.push({ exp: next, coeff: coeff.mul(new CFrac(BigInt(e))) });
  }
  return P.fromTerms(terms);
}

// Полное разложение: содержимое, кратности, потом каждая бесквадратная часть.
export function factorFully(poly, rnd) {
  const { content, primitive } = contentAndPrimitive(poly);
  const out = [];
  if (!collectFactors(primitive, rnd, out)) return null;
  return { content, factors: out };
}

// МНОЖИТЕЛИ БЕЗ ПЕРВОЙ ПЕРЕМЕННОЙ — ОТДЕЛЬНО И СНАЧАЛА.
//
// Кратности ищутся через производную по первой переменной, а множитель, в
// котором её нет, целиком уходит в НОД с этой производной — и терялся: у
// «OI ∥ BC» из −(y − z)(y + z)(…) «полное» разложение печатало одну скобку.
// Поэтому содержимое по первой переменной раскладывается само по себе, а
// кратности считаются уже у примитивной части, где от неё зависит всё.
function collectFactors(poly, rnd, out) {
  const vars = varsOf(poly);
  if (vars.length === 0) return true;
  let rest = poly;
  const cont = contentIn(poly, vars[0]);
  if (varsOf(cont).length) {
    if (!collectFactors(primitivePart(cont), rnd, out)) return false;
    rest = divideExact(poly, cont);
    if (!rest) return false;
  }
  const parts = squarefreeSplit(rest);
  if (!parts) return false;
  for (const { poly: part, power } of parts) {
    const pieces = factorSquarefree(part, rnd);
    if (!pieces) return false;
    for (const piece of pieces) out.push({ poly: piece, power });
  }
  return true;
}

function contentIn(poly, v) {
  let g = P.zero();
  for (const c of P.coeffsIn(poly, v)) {
    if (c.isZero()) continue;
    g = polyGcd(g, c);
    if (P.isOne(g)) break;
  }
  return g.isZero() ? P.constant(ONE) : g;
}

// Бесквадратное разложение над Q(i): НОД с производной отделяет кратности.
function squarefreeSplit(poly) {
  const vars = varsOf(poly);
  if (vars.length === 0) return [];
  const v = vars[0];
  let d = P.zero();
  for (const u of vars) d = P.add(d, derivativeIn(poly, u));
  if (d.isZero()) return [{ poly, power: 1 }];

  let c = polyGcd(poly, derivativeIn(poly, v));
  let w = divideExact(poly, c);
  if (!w) return [{ poly, power: 1 }];
  const out = [];
  let power = 1;
  while (!P.isOne(w)) {
    checkComputeBudget();
    const y = polyGcd(w, c);
    const z = divideExact(w, y);
    if (!z) return null;
    if (!P.isOne(z)) out.push({ poly: primitivePart(z), power });
    w = y;
    const next = divideExact(c, y);
    if (!next) return null;
    c = next;
    power++;
    if (power > 64) return null;
  }
  return out;
}
