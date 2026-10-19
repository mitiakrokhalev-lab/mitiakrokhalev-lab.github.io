// Модулярный многомерный НОД: схема Брауна поверх конечного поля.
//
// Зачем он, если НОД уже есть. Последовательность псевдоостатков считает
// правильно, но коэффициенты по дороге раздуваются: на реальной задаче
// (окружность через вершину и два основания чевиан) счёт доходил до тысяч
// знаков в числах и не заканчивался вовсе. Причём цена зависела от ПОРЯДКА
// БУКВ: та же геометрия при другом назначении a, b, c считалась за секунды.
// Это верный признак, что упираемся не в задачу, а в алгоритм.
//
// Здесь коэффициенты не растут в принципе. Схема стандартная:
//
//   1) считаем НОД по нескольким простым — в конечном поле числа машинные;
//   2) внутри каждого простого рекурсивно избавляемся от переменных
//      ПОДСТАНОВКОЙ, а ответ собираем интерполяцией Ньютона;
//   3) образы склеиваем китайской теоремой об остатках;
//   4) ответ ПРОВЕРЯЕМ делением — и только после этого отдаём.
//
// Пункт 4 — не перестраховка, а то, что делает всю конструкцию честной. Ни
// «неудачное простое», ни «неудачная точка подстановки» не могут дать неверный
// ответ: они могут дать только БОЛЬШИЙ (кандидат делится хуже), а деление это
// ловит. Обратная сторона той же монеты — самый частый случай «НОД равен
// единице» становится бесплатным: если образ равен единице хоть при одном
// хорошем простом, то и настоящий НОД равен единице, и проверять нечего.
//
// Считает всё это упакованный слой из modpoly.js: одночлен — число,
// коэффициент — число. Общий poly.js здесь не годится по цене — см. его шапку.
//
// Порядок одночленов всюду один и тот же — полная степень, потом показатели.
// Он мультипликативен, поэтому старший одночлен произведения равен произведению
// старших, а на этом держится вся работа со старшими коэффициентами ниже.

import * as P from './poly.js';
import { CFrac, ONE } from './complex-fraction.js';
import { Fraction } from './fraction.js';
import { checkComputeBudget } from './budget.js';
import { makeField, primeAt } from './fp2.js';
import { makePacking, makeOps, CeilingExceeded, trimArr, evalArray, scaleArray,
  subArray, addArrayInto, mulByLinear, evalRows, addOuter } from './modpoly.js';
import { primitivePart, divideExact, mainVar, gaussGcd, gz, gzIsZero } from './polyint.js';

const PRIME_LIMIT = 512;

// ---- форма образа ----------------------------------------------------------

// Вектор степеней по активным переменным. Сравнение по компонентам отличает
// неудачную точку (форма БОЛЬШЕ настоящей) от удачной, и это единственная
// защита, которая нужна: меньше настоящей форма стать не может.
function shapeOf(ops, x, active) {
  return active.map(j => ops.degreeIn(x, j));
}

function compareShape(x, y) {
  let less = false, more = false;
  for (let i = 0; i < x.length; i++) {
    if (x[i] < y[i]) less = true;
    if (x[i] > y[i]) more = true;
  }
  if (less && more) return null;        // несравнимы — считаем неудачей
  if (less) return -1;
  if (more) return 1;
  return 0;
}

// ---- НОД по модулю одного простого ----------------------------------------

function gcdField(ops, A, B, active, rnd) {
  checkComputeBudget();
  const F = ops.F;
  if (A.size === 0) return ops.monic(B);
  if (B.size === 0) return ops.monic(A);
  if (active.length === 0) return ops.constant(F.one);
  if (active.length === 1) {
    const j = active[0];
    return ops.fromArray(ops.gcdArray(ops.toArray(A, j), ops.toArray(B, j)), j);
  }
  if (active.length === 2) return gcdTwoVars(ops, A, B, active, rnd);

  // Исключаем переменную с НАИБОЛЬШЕЙ степенью. Число узлов рекурсии от порядка
  // не зависит (это произведение по всем переменным), а вот размер многочленов
  // на верхних уровнях — зависит: подстановка в самую «толстую» переменную
  // ужимает их сильнее всего, и вся работа ниже идёт по меньшим данным.
  // Замерено на чевианах: по наибольшей — 0.86 с, по наименьшей — 1.31 с.
  let v = active[0];
  let heaviest = -1;
  for (const j of active) {
    const weight = ops.degreeIn(A, j) + ops.degreeIn(B, j);
    if (weight > heaviest) { heaviest = weight; v = j; }
  }
  const rest = active.filter(j => j !== v);

  // Содержимое ПО x_v — то есть НОД коэффициентов при одночленах от остальных
  // переменных. Снимать надо именно его: интерполянт отличается от настоящего
  // НОДа множителем, зависящим ТОЛЬКО от переменной подстановки, и убрать его
  // можно лишь содержимым в этом смысле. (Первая версия снимала содержимое по
  // остальным переменным — ответ не делил исходные, проверка его отвергала, и
  // весь модулярный путь молча отваливался в старый.)
  //
  // Приятный побочный эффект: каждый такой коэффициент — многочлен от ОДНОЙ
  // переменной, поэтому содержимое считается одномерным Евклидом, а не
  // рекурсией по всем переменным.
  const cA = contentInVar(ops, A, v);
  const cB = contentInVar(ops, B, v);
  const A1 = divideByUni(ops, A, cA, v);
  const B1 = divideByUni(ops, B, cB, v);
  if (!A1 || !B1) return null;
  const common = gcdInVar(ops, cA, cB, v);
  const delta = gcdInVar(ops, ops.leadIn(A1, v), ops.leadIn(B1, v), v);

  const dv = Math.min(ops.degreeIn(A1, v), ops.degreeIn(B1, v));
  const maxPoints = dv + ops.degreeIn(delta, v) + 1;

  let interp = new Map();
  let basis = ops.constant(F.one);        // ∏ (x_v − α) по уже взятым точкам
  let shape = null;
  let used = 0;
  const seen = new Set();

  for (let guard = 0; used <= maxPoints && guard < 8 * maxPoints + 64; guard++) {
    checkComputeBudget();
    const raw = rnd(F.p - 1) + 1;
    if (seen.has(raw)) continue;
    seen.add(raw);
    const alpha = F.of(raw);

    // Точка, обнуляющая delta, годится только на то, чтобы всё испортить:
    // именно в ней старший коэффициент настоящего НОДа может пропасть.
    const dValue = valueAt(ops, delta, v, alpha);
    if (dValue === 0) continue;

    const image = gcdField(ops, ops.evalVar(A1, v, alpha), ops.evalVar(B1, v, alpha), rest, rnd);
    if (!image) return null;

    const here = shapeOf(ops, image, rest);
    if (shape !== null) {
      const cmp = compareShape(here, shape);
      if (cmp === null || cmp > 0) continue;          // точка неудачная — мимо
      if (cmp < 0) {                                   // неудачными были ПРЕЖНИЕ
        interp = new Map();
        basis = ops.constant(F.one);
        used = 0;
      }
    }
    shape = here;

    // Домножаем образ на delta(α): именно это делает набор образов значениями
    // ОДНОГО многочлена, а не набором случайно нормированных.
    const scaled = ops.scaleBy(image, dValue);

    const err = ops.sub(scaled, ops.evalVar(interp, v, alpha));
    if (err.size > 0) {
      const at = valueAt(ops, basis, v, alpha);
      interp = ops.add(interp, ops.mul(basis, ops.scaleBy(err, F.inv(at))));
    } else if (used > 0) {
      // Новая точка ничего не изменила — похоже, интерполяция сошлась.
      const candidate = attempt(ops, interp, v, common, A1, B1);
      if (candidate) return candidate;
    }

    basis = ops.mul(basis, ops.sub(ops.variable(v), ops.constant(alpha)));
    used++;
  }

  return attempt(ops, interp, v, common, A1, B1);
}

// ---- узел с двумя переменными: всё в плоских массивах ----------------------
//
// Сюда приходится подавляющая часть работы: замер на эталонной задаче дал 6977
// узлов рекурсии, из них 5516 листьев (одна переменная) и 1152 двупеременных —
// вместе 96%. Данных в таком узле на десяток чисел, а платили мы за них
// картами: подстановка строила карту, одномерный НОД разбирал её обратно в
// массив и снова собирал карту, интерполяция опять работала картами. Выходило
// 57.6 микросекунды на узел при разумном поле около десяти.
//
// Здесь весь узел считается на массивах: строка — степень по переменной
// подстановки, столбец — по второй. Карты остаются ровно на входе и выходе, то
// есть ОДИН раз на узел, а не на каждую точку. Алгоритм тот же самый, слово в
// слово: содержимое, delta, интерполяция Ньютона, проверка делением.
function gcdTwoVars(ops, A, B, active, rnd) {
  const F = ops.F;
  let [u, v] = active;
  // Исключаем «толстую», как и на верхних уровнях.
  if (ops.degreeIn(A, u) + ops.degreeIn(B, u) > ops.degreeIn(A, v) + ops.degreeIn(B, v)) {
    [u, v] = [v, u];
  }

  // Разовая часть остаётся на картах: она считается по разу на узел, и
  // переписывать её значило бы дублировать уже проверенный код.
  const cA = contentInVar(ops, A, v);
  const cB = contentInVar(ops, B, v);
  const A1 = divideByUni(ops, A, cA, v);
  const B1 = divideByUni(ops, B, cB, v);
  if (!A1 || !B1) return null;
  const common = gcdInVar(ops, cA, cB, v);
  const delta = ops.toArray(gcdInVar(ops, ops.leadIn(A1, v), ops.leadIn(B1, v), v), v);

  const rowsA = toRows(ops, A1, v, u);
  const rowsB = toRows(ops, B1, v, u);

  const dv = Math.min(rowsA.length, rowsB.length) - 1;
  const maxPoints = dv + delta.length;          // deg delta + dv + 1

  let interp = [];
  let basis = [F.one];
  let shape = -1;
  let used = 0;
  const seen = new Set();

  for (let guard = 0; used <= maxPoints && guard < 8 * maxPoints + 64; guard++) {
    checkComputeBudget();
    const raw = rnd(F.p - 1) + 1;
    if (seen.has(raw)) continue;
    seen.add(raw);
    const alpha = F.of(raw);

    const dValue = evalArray(F, delta, alpha);
    if (dValue === 0) continue;

    const ga = evalRows(F, rowsA, alpha);
    const gb = evalRows(F, rowsB, alpha);
    if (ga.length === 0 || gb.length === 0) continue;

    const image = ops.gcdArray(ga, gb);
    const here = image.length - 1;
    if (shape >= 0) {
      if (here > shape) continue;                       // точка неудачная
      if (here < shape) { interp = []; basis = [F.one]; used = 0; }
    }
    shape = here;

    const err = subArray(F, scaleArray(F, image, dValue), evalRows(F, interp, alpha));
    if (err.length > 0) {
      const at = evalArray(F, basis, alpha);
      addOuter(F, interp, basis, scaleArray(F, err, F.inv(at)));
    } else if (used > 0) {
      const candidate = attempt(ops, rowsToMap(ops, interp, v, u), v, common, A1, B1);
      if (candidate) return candidate;
    }

    basis = mulByLinear(F, basis, alpha);
    used++;
  }

  return attempt(ops, rowsToMap(ops, interp, v, u), v, common, A1, B1);
}

function toRows(ops, map, v, u) {
  const rows = [];
  for (const [key, c] of map) {
    const ev = ops.expOf(key, v), eu = ops.expOf(key, u);
    let row = rows[ev];
    if (!row) row = rows[ev] = [];
    row[eu] = ops.F.add(row[eu] ?? 0, c);
  }
  for (let i = 0; i < rows.length; i++) if (!rows[i]) rows[i] = [];
  return rows;
}

function rowsToMap(ops, rows, v, u) {
  const { scale } = ops.packing;
  const out = new Map();
  for (let ev = 0; ev < rows.length; ev++) {
    const row = rows[ev];
    if (!row) continue;
    for (let eu = 0; eu < row.length; eu++) {
      const c = row[eu];
      if (!c) continue;
      out.set(ev * scale[v] + eu * scale[u], c);
    }
  }
  return out;
}

// Одномерный НОД двух многочленов от одной переменной x_v.
function gcdInVar(ops, A, B, v) {
  return ops.fromArray(ops.gcdArray(ops.toArray(A, v), ops.toArray(B, v)), v);
}

// Деление на многочлен от ОДНОЙ переменной — самый частый случай деления в
// схеме: так снимается содержимое по x_v, и так же снимается лишний множитель
// с интерполянта. Общая рекурсия по переменным здесь не нужна и дорога:
// достаточно разложить делимое на «столбцы» (по одночленам от остальных
// переменных) и поделить каждый столбец одномерно.
//
// Профиль до этого показывал в общем делении почти треть всего времени НОДа —
// и две трети его вызовов приходились именно на этот случай.
function divideByUni(ops, A, divisor, v) {
  const F = ops.F;
  const arr = ops.toArray(divisor, v);
  if (arr.length === 0) return null;
  if (arr.length === 1) {                       // делитель — константа
    return arr[0] === F.one ? A : ops.scaleBy(A, F.inv(arr[0]));
  }

  const columns = new Map();
  for (const [key, c] of A) {
    const rest = ops.clearVar(key, v);
    const e = ops.expOf(key, v);
    let col = columns.get(rest);
    if (!col) { col = []; columns.set(rest, col); }
    while (col.length <= e) col.push(0);
    col[e] = F.add(col[e], c);
  }

  const { scale } = ops.packing;
  const out = new Map();
  for (const [rest, col] of columns) {
    while (col.length > 0 && !col[col.length - 1]) col.pop();
    const quotient = ops.divideArray(col, arr);
    if (!quotient) return null;                 // столбец не поделился нацело
    for (let e = 0; e < quotient.length; e++) {
      if (quotient[e]) out.set(rest + e * scale[v], quotient[e]);
    }
  }
  return out;
}


// Значение многочлена от ОДНОЙ переменной в точке — просто элемент поля.
function valueAt(ops, poly, v, alpha) {
  const value = ops.evalVar(poly, v, alpha);
  return value.size === 0 ? 0 : value.get(0) ?? 0;
}

// Кандидат из интерполянта: снять содержимое по x_v (оно там от домножения на
// delta) и проверить делением. Проверка обязательна — без неё сюда прошёл бы
// результат неудачной точки.
//
// Проверяем ПРИМИТИВНУЮ часть против ПРИМИТИВНЫХ же A₁ и B₁, а общее содержимое
// приписываем уже к проверенному. Против исходных A и B это не сработало бы:
// общее содержимое — многочлен от одной x_v, и примитивную часть он не делит
// (наступил на это, отладка стоила целого прогона).
function attempt(ops, interp, v, common, A1, B1) {
  if (interp.size === 0) return null;
  const primitive = divideByUni(ops, interp, contentInVar(ops, interp, v), v);
  if (!primitive) return null;
  if (!ops.divideExact(A1, primitive) || !ops.divideExact(B1, primitive)) return null;
  return ops.monic(ops.mul(common, primitive));
}

// Содержимое по x_v: НОД коэффициентов при одночленах от ОСТАЛЬНЫХ переменных.
// Каждый такой коэффициент — многочлен от одной x_v, поэтому весь счёт здесь
// одномерный.
function contentInVar(ops, poly, v) {
  const F = ops.F;
  const groups = new Map();
  for (const [key, coeff] of poly) {
    const rest = ops.clearVar(key, v);
    const e = ops.expOf(key, v);
    let arr = groups.get(rest);
    if (!arr) { arr = []; groups.set(rest, arr); }
    while (arr.length <= e) arr.push(0);
    arr[e] = F.add(arr[e], coeff);
  }
  let g = null;
  for (const arr of groups.values()) {
    checkComputeBudget();
    while (arr.length > 0 && arr[arr.length - 1] === 0) arr.pop();
    g = g === null ? arr : ops.gcdArray(g, arr);
    if (g.length <= 1) break;                  // константа — дальше некуда
  }
  return ops.fromArray(g === null || g.length === 0 ? [F.one] : g, v);
}

// ---- дешёвая проба на взаимную простоту ------------------------------------
//
// Подавляющее большинство вызовов НОДа отвечает «единица», и платить за это
// полной схемой Брауна нельзя: контроль показал, что тяжёлые тесты на
// расширения от этого дорожают вдвое.
//
// Подставляем случайные числа во все переменные, кроме одной, и смотрим СТЕПЕНЬ
// одномерного НОДа. Настоящий НОД делит оба многочлена, значит после подстановки
// он делит и образы, значит степень образа не меньше его собственной. Ноль по
// КАЖДОЙ переменной ⟹ НОД — константа, а у примитивных многочленов это единица.
//
// Оговорка одна: точка не должна съедать старший коэффициент по этой
// переменной — иначе степень образа может оказаться меньше настоящей. Это
// проверяется прямо, и при неудаче проба честно отвечает «не знаю».
function probeCoprime(ops, A, B, active, rnd) {
  const F = ops.F;
  for (const v of active) {
    let a = A, b = B;
    for (const u of active) {
      if (u === v) continue;
      const point = F.of(rnd(F.p - 1) + 1);
      a = ops.evalVar(a, u, point);
      b = ops.evalVar(b, u, point);
    }
    if (a.size === 0 || b.size === 0) return false;
    if (ops.degreeIn(a, v) !== ops.degreeIn(A, v)) return false;
    if (ops.degreeIn(b, v) !== ops.degreeIn(B, v)) return false;
    if (ops.gcdArray(ops.toArray(a, v), ops.toArray(b, v)).length > 1) return false;
  }
  return true;
}

// ---- перевод в поле и обратно ----------------------------------------------

function toField(poly, ops, packing) {
  const { vars, scale, cap } = packing;
  const out = new Map();
  for (const { exp, coeff } of P.terms(poly)) {
    const c = ops.F.ofCFrac(coeff);
    if (c === null) return null;               // простое делит знаменатель
    if (c === 0) continue;
    let key = 0;
    for (let j = 0; j < vars.length; j++) {
      const e = exp[vars[j]] ?? 0;
      if (e >= cap[j]) return null;            // не влезает в раскладку
      key += e * scale[j];
    }
    out.set(key, c);
  }
  return out;
}

// Старший одночлен ИСХОДНОГО многочлена в том же порядке, что и в поле.
function leadKeyOuter(poly, ops, packing) {
  const { vars, scale, cap } = packing;
  let best = -1;
  for (const { exp } of P.terms(poly)) {
    let key = 0;
    for (let j = 0; j < vars.length; j++) {
      const e = exp[vars[j]] ?? 0;
      if (e >= cap[j]) return -1;
      key += e * scale[j];
    }
    if (best < 0 || ops.compare(key, best, -1) < 0) best = key;
  }
  return best;
}

// ---- подъём китайской теоремой --------------------------------------------

function invMod(a, m) {
  let [old, cur] = [((a % m) + m) % m, m];
  let [x, nx] = [1n, 0n];
  while (cur) {
    const q = old / cur;
    [old, cur] = [cur, old - q * cur];
    [x, nx] = [nx, x - q * nx];
  }
  return ((x % m) + m) % m;
}

// Симметричный представитель: коэффициенты настоящего НОДа малы по модулю, и
// именно в симметричном виде они и появляются.
function symmetric(value, mod) {
  const half = mod / 2n;
  return value > half ? value - mod : value;
}

function crt(lifted, modulus, image, ops, p) {
  const F = ops.F;
  const fresh = new Map();
  for (const [key, coeff] of image) {
    fresh.set(key, { re: BigInt(F.re(coeff)), im: BigInt(F.im(coeff)) });
  }
  if (lifted === null || modulus === 0n) return fresh;

  const out = new Map();
  const inv = invMod(modulus % p, p);
  const keys = new Set([...lifted.keys(), ...fresh.keys()]);
  for (const key of keys) {
    const old = lifted.get(key);
    const now = fresh.get(key);
    const combine = (o, n) => {
      const base = ((o % modulus) + modulus) % modulus;
      const diff = (((n - base) % p) + p) % p;
      return base + modulus * ((diff * inv) % p);
    };
    out.set(key, {
      re: combine(old ? old.re : 0n, now ? now.re : 0n),
      im: combine(old ? old.im : 0n, now ? now.im : 0n),
    });
  }
  return out;
}

function fromLift(lifted, modulus, ops, packing) {
  const { vars } = packing;
  const terms = [];
  for (const [key, { re, im }] of lifted) {
    const r = symmetric(((re % modulus) + modulus) % modulus, modulus);
    const i = symmetric(((im % modulus) + modulus) % modulus, modulus);
    if (r === 0n && i === 0n) continue;
    const exps = ops.keyExps(key);
    const exp = [];
    for (let j = 0; j < vars.length; j++) {
      while (exp.length <= vars[j]) exp.push(0);
      exp[vars[j]] = exps[j];
    }
    terms.push({ exp, coeff: new CFrac(new Fraction(r, 1n), new Fraction(i, 1n)) });
  }
  return P.fromTerms(terms);
}

// ---- вход ------------------------------------------------------------------

// Возвращает НОД (примитивный, с канонической единицей) или null — «не вышло,
// считай прежним способом». Оба аргумента обязаны быть примитивными над Z[i].
export function modularGcd(A, B) {
  const vars = [];
  const budgets = [];
  const top = Math.max(mainVar(A), mainVar(B));
  for (let v = 0; v <= top; v++) {
    const dA = P.degreeIn(A, v), dB = P.degreeIn(B, v);
    if (dA === 0 && dB === 0) continue;
    vars.push(v);
    // Запас вдвое: интерполянт и промежуточные произведения растут, но не
    // больше суммы степеней входов.
    budgets.push(2 * Math.max(dA, dB) + 2);
  }
  if (vars.length === 0) return P.constant(ONE);

  // Показатели не влезли в раскладку — это ПОТОЛОК, и о нём надо сказать вслух.
  // Молчаливый уход в старый путь был бы худшим из вариантов: там та же задача
  // считается часами, и снаружи это выглядит как зависание без объяснения.
  const packing = makePacking(vars, budgets);
  if (!packing) {
    throw new CeilingExceeded(vars.length, Math.max(...budgets.map(b => (b - 2) / 2)));
  }

  const gamma = gaussGcd(toGz(P.leadingCoeff(A)), toGz(P.leadingCoeff(B)));
  if (gzIsZero(gamma)) return null;

  const active = vars.map((_, j) => j);
  let modulus = 0n;
  let lifted = null;
  let shape = null;

  // Простых берём столько, сколько понадобится. Останов гарантирован не
  // потолком, а теоремой: у настоящего НОДа коэффициенты конечны, и как только
  // произведение простых перевалит за их удвоенный максимум, склейка китайской
  // теоремой даёт ТОЧНО его — а проверка делением это подтверждает. Заранее
  // считать эту границу незачем: она нужна была бы, только чтобы знать, когда
  // сдаться, а сдаваться здесь больше не предполагается.
  //
  // Потолок ниже — не ограничение, а сигнал о поломке: пятьсот двенадцать
  // простых это модуль в двенадцать тысяч бит, то есть коэффициенты в четыре
  // тысячи знаков. Такой НОД не поместится в память задолго до этого места,
  // так что дойти сюда можно только по ошибке — и об ошибке надо кричать, а не
  // молча возвращать ответ похуже.
  for (let index = 0; ; index++) {
    if (index >= PRIME_LIMIT) {
      throw new Error('модулярный НОД: простые не сходятся — это ошибка в алгоритме');
    }
    checkComputeBudget();
    const p = primeAt(index);
    const F = makeField(p);
    const ops = makeOps(F, packing);
    const a = toField(A, ops, packing), b = toField(B, ops, packing);
    if (!a || !b) continue;
    // Простое, съевшее старший одночлен, опасно: оно способно занизить НОД, а
    // занижение — единственная ошибка, которую проверка делением НЕ ловит.
    if (ops.leadKey(a, -1) !== leadKeyOuter(A, ops, packing)) continue;
    if (ops.leadKey(b, -1) !== leadKeyOuter(B, ops, packing)) continue;

    // Сначала дешёвая проба: она отвечает на самый частый вопрос за микросекунды.
    if (modulus === 0n && probeCoprime(ops, a, b, active, rng(p ^ 0x5bf03635))) {
      return P.constant(ONE);
    }

    const image = gcdField(ops, a, b, active, rng(p ^ 0x9e3779b9));
    if (!image) continue;

    // Единица по хорошему простому — это единица и на самом деле: по модулю
    // НОД может только вырасти.
    if (ops.isOne(image)) return P.constant(ONE);

    const here = shapeOf(ops, image, active);
    if (shape !== null) {
      const cmp = compareShape(here, shape);
      if (cmp === null || cmp > 0) continue;      // неудачное простое
      if (cmp < 0) { lifted = null; modulus = 0n; }   // неудачными были прежние
    }
    shape = here;

    const scaled = ops.scaleBy(image, F.mul(F.ofGz(gamma), F.inv(ops.leadCoeff(image))));
    lifted = crt(lifted, modulus, scaled, ops, BigInt(p));
    modulus = modulus === 0n ? BigInt(p) : modulus * BigInt(p);

    const candidate = primitivePart(fromLift(lifted, modulus, ops, packing));
    if (candidate.isZero()) continue;
    if (divideExact(A, candidate) && divideExact(B, candidate)) return candidate;
  }
  return null;
}

function toGz(coeff) {
  // Примитивная часть уже без знаменателей, поэтому числители и есть гауссово
  // целое; проверку оставляем на случай, если сюда придёт что-то другое.
  if (coeff.re.d !== 1n || coeff.im.d !== 1n) return gz(0n, 0n);
  return gz(coeff.re.n, coeff.im.n);
}

// Точки подстановки берём псевдослучайно, но ВОСПРОИЗВОДИМО: иначе один и тот
// же счёт то проходил бы, то нет, и отлаживать было бы нечего.
function rng(seed) {
  let s = (seed >>> 0) || 1;
  return n => {
    s = (Math.imul(s, 1103515245) + 12345) & 0x7fffffff;
    return s % n;
  };
}
