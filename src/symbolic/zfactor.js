// Разложение одномерного многочлена над ГАУССОВЫМИ ЦЕЛЫМИ.
//
// Второй этап полного разложения. Первый (unifactor.js) умеет раскладывать по
// модулю простого; здесь этот ответ поднимается до настоящих целых.
//
// Схема:
//
//   1) выбрать простое, при котором многочлен не теряет степень и остаётся
//      свободным от квадратов;
//   2) разложить его по этому простому;
//   3) ПОДНЯТЬ разложение с p до p^k (подъём Гензеля): по модулю p множители
//      известны, и каждый шаг уточняет их на один порядок, оставаясь верным
//      по модулю следующей степени;
//   4) СОБРАТЬ настоящие множители из поднятых. Это не просто «взять каждый»:
//      неприводимый над Z[i] многочлен по модулю может распасться на несколько
//      кусков, поэтому перебираются ПОДМНОЖЕСТВА, а годность каждого кандидата
//      решается точным делением.
//
// Где остановиться, говорит оценка Миньотта: коэффициенты любого делителя
// ограничены сверху величиной, считаемой по самому многочлену. Как только p^k
// перевалит за удвоенную оценку, симметричный представитель по модулю p^k — это
// уже настоящий коэффициент, а не его остаток.

import { checkComputeBudget } from './budget.js';
import { makeField, primeAt, isFieldPrime } from './fp2.js';
import { trimArr, arrayOps } from './modpoly.js';

// Арифметика массивов специализируется по полю (см. modpoly.js), поэтому берём
// её один раз на поле, а не на каждый вызов.
const opsCache = new WeakMap();
function ops(F) {
  let value = opsCache.get(F);
  if (!value) { value = arrayOps(F); opsCache.set(F, value); }
  return value;
}

import { factorUnivariate } from './unifactor.js';

// ---- арифметика над Z[i] на массивах ---------------------------------------
//
// Коэффициент — пара bigint-ов. Многочлен — массив коэффициентов по степеням.

const gz = (re, im) => ({ re, im });
const zZero = gz(0n, 0n);
const isZeroC = c => c.re === 0n && c.im === 0n;
const addC = (x, y) => gz(x.re + y.re, x.im + y.im);
const subC = (x, y) => gz(x.re - y.re, x.im - y.im);
const mulC = (x, y) => gz(x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re);
const absBig = x => (x < 0n ? -x : x);

const trimZ = a => { while (a.length > 0 && isZeroC(a[a.length - 1])) a.pop(); return a; };

function addZ(a, b) {
  const out = new Array(Math.max(a.length, b.length));
  for (let i = 0; i < out.length; i++) out[i] = addC(a[i] ?? zZero, b[i] ?? zZero);
  return trimZ(out);
}

function subZ(a, b) {
  const out = new Array(Math.max(a.length, b.length));
  for (let i = 0; i < out.length; i++) out[i] = subC(a[i] ?? zZero, b[i] ?? zZero);
  return trimZ(out);
}

function mulZ(a, b) {
  if (a.length === 0 || b.length === 0) return [];
  const out = new Array(a.length + b.length - 1).fill(zZero);
  for (let i = 0; i < a.length; i++) {
    if (isZeroC(a[i])) continue;
    for (let j = 0; j < b.length; j++) {
      if (isZeroC(b[j])) continue;
      out[i + j] = addC(out[i + j], mulC(a[i], b[j]));
    }
  }
  return trimZ(out);
}

function scaleZ(a, c) {
  if (isZeroC(c)) return [];
  return trimZ(a.map(x => mulC(x, c)));
}

// Симметричный остаток по модулю m: коэффициент настоящего множителя мал, и
// именно в симметричном виде он и появляется.
function modSym(value, m) {
  let r = ((value % m) + m) % m;
  if (2n * r > m) r -= m;
  return r;
}

const modZ = (a, m) => trimZ(a.map(c => gz(modSym(c.re, m), modSym(c.im, m))));

// Деление нацело на гауссово целое; null, если хоть один коэффициент не делится.
function divideByC(a, c) {
  const norm = c.re * c.re + c.im * c.im;
  const out = [];
  for (const x of a) {
    const re = x.re * c.re + x.im * c.im;
    const im = x.im * c.re - x.re * c.im;
    if (re % norm !== 0n || im % norm !== 0n) return null;
    out.push(gz(re / norm, im / norm));
  }
  return trimZ(out);
}

// Точное деление многочленов над Z[i]: null, если не делится.
function divideZ(a, b) {
  if (b.length === 0) return null;
  if (a.length === 0) return [];
  if (a.length < b.length) return null;
  const lead = b[b.length - 1];
  const rem = a.slice();
  const quot = new Array(a.length - b.length + 1).fill(zZero);
  for (let k = rem.length - 1; k >= b.length - 1; k--) {
    if (isZeroC(rem[k])) continue;
    const step = divideByC([rem[k]], lead);
    if (!step || step.length === 0) return null;
    const factor = step[0];
    quot[k - b.length + 1] = factor;
    for (let i = 0; i < b.length; i++) {
      rem[k - b.length + 1 + i] = subC(rem[k - b.length + 1 + i], mulC(factor, b[i]));
    }
  }
  for (const c of rem) if (!isZeroC(c)) return null;
  return trimZ(quot);
}

function gcdC(a, b) {
  // Евклид в Z[i]: деление с округлением к ближайшему.
  let x = a, y = b;
  while (!isZeroC(y)) {
    const norm = y.re * y.re + y.im * y.im;
    const round = (num, den) => {
      let q = num / den;
      const r = num - q * den;
      if (2n * absBig(r) >= absBig(den)) q += (r < 0n) === (den < 0n) ? 1n : -1n;
      return q;
    };
    const q = gz(round(x.re * y.re + x.im * y.im, norm), round(x.im * y.re - x.re * y.im, norm));
    const r = subC(x, mulC(q, y));
    x = y; y = r;
  }
  return x;
}

// Множитель определён с точностью до единицы (±1, ±i), и выбор надо
// ЗАФИКСИРОВАТЬ: иначе один и тот же многочлен печатался бы то как (2x+1), то
// как (−2x−1), а тесты ловили бы призраки. Договорённость та же, что и у НОДа
// в polyint.js: старший коэффициент приводится к каноническому виду.
const UNITS = [gz(1n, 0n), gz(0n, 1n), gz(-1n, 0n), gz(0n, -1n)];

function canonicalizeZ(a) {
  if (a.length === 0) return a;
  const lead = a[a.length - 1];
  for (const u of UNITS) {
    const t = mulC(lead, u);
    if (t.re > 0n || (t.re === 0n && t.im > 0n)) return scaleZ(a, u);
  }
  return a;
}

// Содержимое (НОД коэффициентов) и примитивная часть.
export function contentZ(a) {
  let g = zZero;
  for (const c of a) g = gcdC(g, c);
  return g;
}

// ---- перевод в поле и обратно ----------------------------------------------

function toField(F, a) {
  const out = a.map(c => {
    const re = Number(((c.re % BigInt(F.p)) + BigInt(F.p)) % BigInt(F.p));
    const im = Number(((c.im % BigInt(F.p)) + BigInt(F.p)) % BigInt(F.p));
    return F.of(re, im);
  });
  return trimArr(out);
}

function fromField(F, a, p) {
  // Простое приходит и числом, и bigint-ом — приводим на входе, а не в каждом
  // вызове: на этом уже поймали ошибку смешения типов.
  const m = BigInt(p);
  return trimZ(a.map(c => gz(modSym(BigInt(F.re(c)), m), modSym(BigInt(F.im(c)), m))));
}

// ---- оценка Миньотта -------------------------------------------------------
//
// Коэффициенты любого делителя многочлена степени n ограничены величиной
// 2^n · ‖f‖. Оценка грубая, но нам нужна не точность, а гарантия: как только
// модуль превысит её вдвое, симметричный представитель перестаёт быть остатком
// и становится самим числом.
function coefficientBound(f) {
  let norm = 0n;
  for (const c of f) {
    const size = absBig(c.re) + absBig(c.im);
    if (size > norm) norm = size;
  }
  const n = BigInt(f.length);
  const lead = absBig(f[f.length - 1].re) + absBig(f[f.length - 1].im);
  return (1n << (n + 1n)) * norm * (n + 1n) * (lead + 1n);
}

// ---- подъём Гензеля --------------------------------------------------------

// Расширенный Евклид над полем: s·g + t·h = 1.
function bezout(F, g, h) {
  let [r0, r1] = [g.slice(), h.slice()];
  let [s0, s1] = [[F.one], []];
  let [t0, t1] = [[], [F.one]];
  const sub = (a, b) => {
    const out = new Array(Math.max(a.length, b.length));
    for (let i = 0; i < out.length; i++) out[i] = F.sub(a[i] ?? 0, b[i] ?? 0);
    return trimArr(out);
  };
  while (r1.length > 0) {
    const q = divideWithRemainder(F, r0, r1);
    [r0, r1] = [r1, q.rem];
    [s0, s1] = [s1, sub(s0, ops(F).mulArray(q.quot, s1))];
    [t0, t1] = [t1, sub(t0, ops(F).mulArray(q.quot, t1))];
  }
  if (r0.length !== 1) return null;              // не взаимно просты
  const inv = F.inv(r0[0]);
  return { s: s0.map(c => F.mul(c, inv)), t: t0.map(c => F.mul(c, inv)) };
}

function divideWithRemainder(F, a, b) {
  const db = b.length - 1;
  const inv = F.inv(b[db]);
  const rem = a.slice();
  const quot = new Array(Math.max(0, a.length - db)).fill(0);
  for (let k = rem.length - 1; k >= db; k--) {
    if (!rem[k]) continue;
    const factor = F.mul(rem[k], inv);
    quot[k - db] = factor;
    for (let i = 0; i <= db; i++) rem[k - db + i] = F.sub(rem[k - db + i] ?? 0, F.mul(factor, b[i]));
  }
  return { quot: trimArr(quot), rem: trimArr(rem) };
}

// Один шаг подъёма пары: из разложения по модулю m делает разложение по m·p.
function liftStep(F, p, m, f, g, h, s, t) {
  const diff = subZ(f, mulZ(g, h));
  if (diff.length === 0) return { g, h };        // уже точно
  const scaled = divideByC(diff, gz(m, 0n));
  if (!scaled) return null;                      // не кратно m — подъём сорвался
  const c = toField(F, scaled);
  if (c.length === 0) return { g, h };

  const { quot, rem } = divideWithRemainder(F, ops(F).mulArray(c, t), toField(F, g));
  const dg = rem;
  const dh = (() => {
    const base = ops(F).mulArray(c, s);
    const extra = ops(F).mulArray(quot, toField(F, h));
    const out = new Array(Math.max(base.length, extra.length));
    for (let i = 0; i < out.length; i++) out[i] = F.add(base[i] ?? 0, extra[i] ?? 0);
    return trimArr(out);
  })();

  return {
    g: addZ(g, scaleZ(fromField(F, dg, p), gz(m, 0n))),
    h: addZ(h, scaleZ(fromField(F, dh, p), gz(m, 0n))),
  };
}

// Подъём всего списка множителей: делим пополам, поднимаем пару, рекурсия.
function liftAll(F, p, target, f, factors) {
  if (factors.length === 1) return [f];
  const half = Math.ceil(factors.length / 2);
  const left = factors.slice(0, half), right = factors.slice(half);

  const gMod = left.reduce((acc, x) => ops(F).mulArray(acc, x), [F.one]);
  const hMod = right.reduce((acc, x) => ops(F).mulArray(acc, x), [F.one]);
  const bez = bezout(F, gMod, hMod);
  if (!bez) return null;

  // Старший коэффициент отдаём левой половине: произведение обязано совпадать
  // с f не только по модулю, но и по старшему члену.
  const lead = f[f.length - 1];
  let g = scaleZ(fromField(F, gMod, BigInt(p)), lead);
  let h = fromField(F, hMod, BigInt(p));
  g = modZ(g, BigInt(p) ** 1n);

  let m = BigInt(p);
  while (m < target) {
    checkComputeBudget();
    const next = liftStep(F, p, m, f, g, h, bez.s, bez.t);
    if (!next) return null;
    g = modZ(next.g, m * BigInt(p));
    h = modZ(next.h, m * BigInt(p));
    m *= BigInt(p);
  }

  const leftLifted = liftAll(F, p, target, g, left);
  const rightLifted = liftAll(F, p, target, h, right);
  if (!leftLifted || !rightLifted) return null;
  return [...leftLifted, ...rightLifted];
}

// ---- сборка настоящих множителей -------------------------------------------

// Перебираем ПОДМНОЖЕСТВА поднятых кусков: неприводимый над Z[i] многочлен по
// модулю вполне может распасться, поэтому «каждый кусок — множитель» неверно.
// Годность решает точное деление, поэтому ошибиться нельзя: неверный кандидат
// просто не поделит.
function recombine(pieces, f, modulus) {
  const out = [];
  let rest = f;
  const used = new Array(pieces.length).fill(false);

  for (let size = 1; size <= pieces.length; size++) {
    let restart = true;
    while (restart) {
      restart = false;
      const indices = [];
      const walk = (start, left) => {
        if (restart) return;
        if (left === 0) {
          checkComputeBudget();
          let candidate = [gz(rest[rest.length - 1].re, rest[rest.length - 1].im)];
          for (const i of indices) candidate = mulZ(candidate, pieces[i]);
          candidate = modZ(candidate, modulus);
          const cont = contentZ(candidate);
          const primitive = isZeroC(cont) ? candidate : divideByC(candidate, cont) ?? candidate;
          const quotient = divideZ(rest, primitive);
          if (quotient && primitive.length > 1) {
            out.push(primitive);
            rest = quotient;
            for (const i of indices) used[i] = true;
            restart = true;
          }
          return;
        }
        for (let i = start; i < pieces.length; i++) {
          if (used[i]) continue;
          indices.push(i);
          walk(i + 1, left - 1);
          indices.pop();
          if (restart) return;
        }
      };
      walk(0, size);
    }
  }
  if (rest.length > 1) out.push(rest);
  return out;
}

// ---- вход ------------------------------------------------------------------

// Раскладывает БЕСКВАДРАТНЫЙ примитивный многочлен над Z[i] на неприводимые.
// Возвращает список множителей или null, если ни одно простое не подошло.
export function factorSquarefreeOverZi(f, rnd) {
  if (f.length <= 2) return [canonicalizeZ(f)];

  const bound = coefficientBound(f);
  for (let attempt = 0; attempt < 20; attempt++) {
    checkComputeBudget();
    const p = primeAt(attempt);
    const F = makeField(p);
    const image = toField(F, f);
    if (image.length !== f.length) continue;          // простое съело старший член

    // По модулю тоже обязан быть свободен от квадратов, иначе подъём не
    // определён однозначно.
    const derivative = trimArr(image.map((c, i) => (i === 0 ? 0 : F.mul(c, F.of(i)))).slice(1));
    if (derivative.length === 0) continue;
    if (ops(F).gcdArray(image, derivative).length !== 1) continue;

    const modular = factorUnivariate(F, image, rnd);
    if (!modular) continue;
    if (modular.length === 1) return [canonicalizeZ(f)];   // неприводим по модулю ⟹ и вообще

    let target = BigInt(p);
    while (target < 2n * bound) target *= BigInt(p);

    const lifted = liftAll(F, p, target, f, modular.map(x => x.poly));
    if (!lifted) continue;

    const pieces = lifted.map(piece => modZ(piece, target));
    return recombine(pieces, f, target).map(canonicalizeZ);
  }
  return null;
}

// Простые для тестов и разбора: полезно знать, что список настоящий.
export { isFieldPrime, divideZ, mulZ, modZ };
