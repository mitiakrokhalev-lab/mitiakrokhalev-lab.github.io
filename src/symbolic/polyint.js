// Многочлены над ГАУССОВЫМИ ЦЕЛЫМИ: содержимое, примитивная часть, точное
// деление. Всё, что нужно и обычному НОДу (gcd.js), и модулярному
// (modgcd.js), — поэтому живёт отдельно: иначе два модуля импортировали бы
// друг друга по кругу, а однофайловая сборка кольцевых импортов не переживает.

import { CFrac, ONE } from './complex-fraction.js';
import { Fraction } from './fraction.js';
import * as P from './poly.js';
import { checkComputeBudget } from './budget.js';
// ---- гауссовы целые -------------------------------------------------------

function bigAbs(x) { return x < 0n ? -x : x; }

function bigRoundDiv(num, den) {
  let q = num / den;
  const r = num - q * den;
  if (2n * bigAbs(r) >= bigAbs(den)) q += (r < 0n) === (den < 0n) ? 1n : -1n;
  return q;
}

const gz = (re, im) => ({ re, im });
const gzIsZero = z => z.re === 0n && z.im === 0n;
const gzMul = (x, y) => gz(x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re);
const gzSub = (x, y) => gz(x.re - y.re, x.im - y.im);

function gzDivRound(a, b) {
  const n = b.re * b.re + b.im * b.im;
  return gz(bigRoundDiv(a.re * b.re + a.im * b.im, n), bigRoundDiv(a.im * b.re - a.re * b.im, n));
}

// Z[i] — евклидово кольцо, так что обычный алгоритм Евклида работает,
// нужно только делить с округлением к ближайшему.
function gaussGcd(a, b) {
  while (!gzIsZero(b)) {
    const r = gzSub(a, gzMul(gzDivRound(a, b), b));
    a = b;
    b = r;
  }
  return a;
}

// НОД определён с точностью до умножения на единицу (±1, ±i). Фиксируем выбор,
// иначе один и тот же многочлен печатался бы то так, то этак.
function canonicalUnit(z) {
  if (gzIsZero(z)) return z;
  let out = z;
  for (let k = 0; k < 3; k++) {
    if (out.re > 0n || (out.re === 0n && out.im > 0n)) break;
    out = gzMul(out, gz(0n, 1n));      // домножаем на i
  }
  return out;
}

// ---- содержимое и примитивная часть --------------------------------------

// Раскладывает многочлен на числовой множитель и часть со взаимно простыми
// целыми гауссовыми коэффициентами и канонической единицей.
export function contentAndPrimitive(poly) {
  if (poly.isZero()) return { content: ONE, primitive: P.zero() };

  let lcm = 1n;
  for (const { coeff } of poly.terms()) {
    lcm = P.bigLcm(lcm, coeff.re.d);
    lcm = P.bigLcm(lcm, coeff.im.d);
  }
  let g = gz(0n, 0n);
  for (const { coeff } of poly.terms()) {
    g = gaussGcd(g, gz(coeff.re.n * (lcm / coeff.re.d), coeff.im.n * (lcm / coeff.im.d)));
  }
  g = canonicalUnit(g);

  // старший член (в каноническом порядке) тоже приводим к канонической единице
  const lead = P.leadingCoeff(poly);
  const leadScaled = gz(lead.re.n * (lcm / lead.re.d), lead.im.n * (lcm / lead.im.d));
  const q = gzDivRound(leadScaled, g);
  const unit = canonicalUnit(q);
  if (!gzIsZero(q) && (unit.re !== q.re || unit.im !== q.im)) {
    // подобрать множитель-единицу так, чтобы старший коэффициент стал каноничным
    for (const u of [gz(0n, 1n), gz(-1n, 0n), gz(0n, -1n)]) {
      const t = gzMul(q, u);
      if (t.re > 0n || (t.re === 0n && t.im > 0n)) { g = gzMul(g, gz(u.re, -u.im)); break; }
    }
  }

  const content = new CFrac(new Fraction(g.re, lcm), new Fraction(g.im, lcm));
  return { content, primitive: P.scale(poly, ONE.div(content)) };
}

export function primitivePart(poly) { return contentAndPrimitive(poly).primitive; }

// ---- точное деление -------------------------------------------------------

function mainVar(poly) {
  let v = -1;
  for (const { exp } of poly.terms()) {
    for (let i = exp.length - 1; i >= 0; i--) {
      if (exp[i] > 0) { v = Math.max(v, i); break; }
    }
  }
  return v;
}

// Делит A на B нацело; null, если не делится. Длинное деление по старшей
// переменной B, коэффициенты делятся рекурсивно (в них этой переменной уже нет).
export function divideExact(A, B) {
  if (B.isZero()) return null;
  if (A.isZero()) return P.zero();
  const v = mainVar(B);
  if (v < 0) return P.scale(A, ONE.div(B.terms()[0].coeff));

  const db = P.degreeIn(B, v);
  const lb = P.coeffsIn(B, v)[db];
  const xv = P.variable(v);
  let rem = A;
  let quot = P.zero();
  for (;;) {
    if (rem.isZero()) return quot;
    // Длинное деление на больших многочленах идёт долго и НОДа внутри не
    // зовёт — своя проверка обязательна.
    checkComputeBudget();
    const dr = P.degreeIn(rem, v);
    if (dr < db) return null;
    const t = divideExact(P.coeffsIn(rem, v)[dr], lb);
    if (!t) return null;
    const term = P.mul(t, P.pow(xv, dr - db));
    quot = P.add(quot, term);
    const next = P.sub(rem, P.mul(term, B));
    if (!next.isZero() && P.degreeIn(next, v) >= dr) return null;   // не сошлось
    rem = next;
  }
}

export function divides(B, A) { return divideExact(A, B) !== null; }

export { gaussGcd, canonicalUnit, gz, gzMul, gzIsZero, gzDivRound, bigAbs, mainVar };
