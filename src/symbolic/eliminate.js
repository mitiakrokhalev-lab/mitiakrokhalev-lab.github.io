import * as P from './poly.js';
import { Rational } from './rational.js';
import { divideExact } from './gcd.js';
import { factorPoly } from './gcd.js';
import { checkComputeBudget } from './budget.js';

// ИСКЛЮЧЕНИЕ ПАРАМЕТРА: параметризация → уравнение кривой.
//
// Локус GeoGebra устроен наоборот к нашему ГМТ. У ГМТ есть условие на точку —
// равенство нулю, — и оно само по себе уравнение кривой. У локуса условия нет:
// есть бегающая точка t и построенная по ней точка Q = f(t). Множество значений
// f — та же кривая, но записана она параметром, а не уравнением.
//
// Уравнение получается исключением t. Точка z лежит на кривой тогда и только
// тогда, когда НАЙДЁТСЯ t, при котором сразу
//     z = f(t)   и   z̄ = f̄(t),
// то есть когда у двух многочленов от t есть общий корень. А общий корень есть
// ровно тогда, когда их результант равен нулю — и вот он-то и есть искомое
// уравнение от z и z̄.
//
// Точно, а не приближённо: коэффициенты остаются выражениями от букв чертежа.
// Степень при этом никак не ограничена — кубика так кубика.

// Результант двух многочленов по одной образующей.
//
// Это определитель матрицы Сильвестра, и считать его надо БЕЗ ДРОБЕЙ: схема
// Барейса делит каждый минор на предыдущий, деление всегда точное, и записи
// остаются многочленами. Через дроби было бы вдвое короче писать и на порядок
// дольше считать — каждое деление звало бы НОД многочленов от всех букв сразу.
export function resultant(a, b, index) {
  const da = P.degreeIn(a, index);
  const db = P.degreeIn(b, index);
  if (da === 0 && db === 0) return null;
  const ca = P.coeffsIn(a, index);
  const cb = P.coeffsIn(b, index);
  const n = da + db;
  const rows = [];
  const blank = () => Array.from({ length: n }, () => P.zero());
  for (let r = 0; r < db; r++) {
    const row = blank();
    for (let k = 0; k <= da; k++) row[r + da - k] = ca[k] ?? P.zero();
    rows.push(row);
  }
  for (let r = 0; r < da; r++) {
    const row = blank();
    for (let k = 0; k <= db; k++) row[r + db - k] = cb[k] ?? P.zero();
    rows.push(row);
  }
  return bareiss(rows);
}

// Определитель без дробей. Перестановка строк схему не ломает: деления
// остаются точными, меняется только знак — а знак у уравнения кривой роли
// не играет.
function bareiss(m) {
  const n = m.length;
  let sign = 1;
  let prev = P.constant(1n);
  for (let k = 0; k < n - 1; k++) {
    checkComputeBudget();
    if (m[k][k].isZero()) {
      let s = -1;
      for (let i = k + 1; i < n; i++) if (!m[i][k].isZero()) { s = i; break; }
      if (s < 0) return P.zero();                  // столбец нулевой — и весь определитель тоже
      [m[k], m[s]] = [m[s], m[k]];
      sign = -sign;
    }
    for (let i = k + 1; i < n; i++) {
      for (let j = k + 1; j < n; j++) {
        const num = P.sub(P.mul(m[i][j], m[k][k]), P.mul(m[i][k], m[k][j]));
        const q = divideExact(num, prev);
        if (!q) return null;                       // деление не сошлось — считать нечем
        m[i][j] = q;
      }
      m[i][k] = P.zero();
    }
    prev = m[k][k];
  }
  const det = m[n - 1][n - 1];
  return sign < 0 ? P.neg(det) : det;
}

// Снять общую степень образующей: t³ + t² = t²(t + 1).
//
// Нужна не для красоты. Сопряжение точки на окружности — это 1/t, и после
// приведения к общему знаменателю в числителе заводится множитель t^k. В
// результанте он превращается в ЛИШНИЙ множитель, зависящий от z, то есть в
// целую постороннюю компоненту кривой — обычно в одну-единственную точку,
// которой хватает, чтобы вся кривая перестала быть вещественной.
function stripPower(poly, index) {
  let min = Infinity;
  for (const { exp } of poly.terms()) min = Math.min(min, exp[index] ?? 0);
  if (!Number.isFinite(min) || min <= 0) return poly;
  const out = [];
  for (const { exp, coeff } of poly.terms()) {
    const e = exp.slice();
    e[index] -= min;
    out.push({ exp: e, coeff });
  }
  return P.fromTerms(out);
}

// Лишние множители: те, где z не встречается вовсе (это просто числа, нулей они
// не добавляют), и повторы (дважды пройденная компонента — та же компонента).
function cleanUp(poly, zIndex, wIndex) {
  const uses = p => P.degreeIn(p, zIndex) > 0 || P.degreeIn(p, wIndex) > 0;
  if (!uses(poly)) return poly;
  const { factors } = factorPoly(poly);
  let out = null;
  for (const { poly: f } of factors) {
    if (!uses(f)) continue;
    out = out ? P.mul(out, f) : f;
  }
  return out ?? poly;
}

// Уравнение кривой, по которой бегает точка value, когда бегает образующая
// tIndex. Возвращает выражение от z (образующая zIndex) и z̄ (wIndex),
// равенство которого нулю и есть ответ, либо null, если кривой не вышло.
export function implicitize(value, tIndex, zIndex, wIndex) {
  if (!value?.num || tIndex < 0 || zIndex < 0 || wIndex < 0) return null;
  const ring = value.ring;
  const z = Rational.fromVariable(ring, zIndex);
  const w = Rational.fromVariable(ring, wIndex);

  // z − f(t) и z̄ − f̄(t): числители, знаменатель в ноль не обращается.
  const a = stripPower(z.sub(value).num, tIndex);
  const b = stripPower(w.sub(value.conjugate()).num, tIndex);
  // Точка от параметра не зависит — это точка, а не кривая.
  if (P.degreeIn(a, tIndex) === 0 || P.degreeIn(b, tIndex) === 0) return null;
  // Параметр обязан быть один: если у бегающей точки сопряжённая независима
  // (свободная точка), то «локус» двумерен и уравнения у него нет.
  if (P.degreeIn(a, tIndex + 1) > 0 && ring.vars[tIndex + 1]?.kind === 'conj') return null;

  const res = resultant(a, b, tIndex);
  if (!res || res.isZero()) return null;
  const clean = cleanUp(res, zIndex, wIndex);
  if (P.degreeIn(clean, zIndex) === 0 && P.degreeIn(clean, wIndex) === 0) return null;
  return new Rational(ring, clean, P.constant(1n));
}
