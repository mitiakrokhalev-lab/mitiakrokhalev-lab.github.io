import * as P from './poly.js';
import { Rational } from './rational.js';

// ГМТ по уравнению: что за кривая получилась и как её нарисовать.
//
// Условие на точки и выражение от координат дают РАВЕНСТВО НУЛЮ — многочлен от
// букв чертежа. Если одну точку объявить бегающей, а остальные закрепить, то это
// равенство и есть уравнение её геометрического места.
//
// Работаем с ЧИСЛИТЕЛЕМ: знаменатель в ноль не обращается (иначе выражение не
// определено), поэтому множество нулей задаёт именно он.
//
// Степень считается по ДВУМ образующим сразу — самой букве и её сопряжённой:
// у свободной точки это две независимые переменные кольца, и «z z̄ + a z̄ + ā z + b»
// имеет степень два, а не один. Второй степени отвечает коника (в частности
// окружность и прямая), и с ней можно работать дальше; третьей и выше —
// алгебраическая кривая, которую мы умеем только нарисовать.

// Разложение по степеням (z, z̄): ключ «p,q» → коэффициент.
export function byPowers(value, i, j) {
  const ring = value.ring;
  const out = new Map();
  let degree = 0;
  for (const { exp, coeff } of value.num.terms()) {
    const p = exp[i] ?? 0;
    const q = j >= 0 ? (exp[j] ?? 0) : 0;
    degree = Math.max(degree, p + q);
    const rest = exp.slice();
    if (i < rest.length) rest[i] = 0;
    if (j >= 0 && j < rest.length) rest[j] = 0;
    const term = new Rational(ring, P.fromTerms([{ exp: rest, coeff }]), P.constant(1n));
    const key = `${p},${q}`;
    out.set(key, (out.get(key) ?? ring.zero()).add(term));
  }
  return { degree, coeff: out };
}

// Коэффициенты коники A z² + B z z̄ + C z̄² + D z + E z̄ + F.
// Возвращает null, если степень выше второй.
export function conicCoeffs(value, i, j) {
  const { degree, coeff } = byPowers(value, i, j);
  if (degree > 2) return { degree, coeffs: null };
  const ring = value.ring;
  const at = (p, q) => coeff.get(`${p},${q}`) ?? ring.zero();
  return {
    degree,
    coeffs: { A: at(2, 0), B: at(1, 1), C: at(0, 2), D: at(1, 0), E: at(0, 1), F: at(0, 0) },
  };
}

// ---- численная часть --------------------------------------------------------

// Комплексное уравнение → ВЕЩЕСТВЕННАЯ коника в тех же координатах.
//
// Кривая задана одним комплексным равенством, а это два вещественных. Настоящая
// кривая получается, когда уравнение ПРОПОРЦИОНАЛЬНО вещественному: тогда после
// умножения на подходящее число оказывается C = conj(A), E = conj(D), а B и F
// вещественны. Множитель ищем по первому ненулевому коэффициенту.
//
// Не сошлось — значит равенство задаёт не кривую, а точки (пересечение двух
// условий) или пусто; рисовать тут нечего, и мы честно говорим об этом.
export function realConic({ A, B, C, D, E, F }, tol = 1e-7) {
  const abs = z => Math.hypot(z.re, z.im);
  const all = [A, B, C, D, E, F];
  const scale = Math.max(...all.map(abs));
  if (!(scale > 0)) return null;
  // Множитель: делаем вещественным первый заметный коэффициент.
  const lead = all.find(z => abs(z) > tol * scale);
  const n = abs(lead);
  const mul = { re: lead.re / n, im: -lead.im / n };            // 1/phase
  const mulBy = z => ({ re: z.re * mul.re - z.im * mul.im, im: z.re * mul.im + z.im * mul.re });
  const [a, b, c, d, e, f] = all.map(mulBy);

  const near = (x, y) => Math.abs(x - y) <= tol * scale;
  if (!near(c.re, a.re) || !near(c.im, -a.im)) return null;
  if (!near(e.re, d.re) || !near(e.im, -d.im)) return null;
  if (!near(b.im, 0) || !near(f.im, 0)) return null;

  // Q = 2Re(a z²) + b|z|² + 2Re(d z) + f, где z = x + iy.
  return {
    xx: 2 * a.re + b.re,
    xy: -4 * a.im,
    yy: b.re - 2 * a.re,
    x: 2 * d.re,
    y: -2 * d.im,
    one: f.re,
  };
}

// Коника из нормированных координат в координаты чертежа: z = (w − o)/r.
export function denormConic(k, ox, oy, r) {
  const s = 1 / r;
  // x = (X − ox)·s, y = (Y − oy)·s
  const xx = k.xx * s * s;
  const xy = k.xy * s * s;
  const yy = k.yy * s * s;
  const x = -2 * k.xx * ox * s * s - k.xy * oy * s * s + k.x * s;
  const y = -2 * k.yy * oy * s * s - k.xy * ox * s * s + k.y * s;
  const one = k.xx * ox * ox * s * s + k.xy * ox * oy * s * s + k.yy * oy * oy * s * s
            - k.x * ox * s - k.y * oy * s + k.one;
  return { xx, xy, yy, x, y, one };
}

// Строка уравнения для GeoGebra. Мелочь, но без неё команда не собирается:
// «+ -3 x» GeoGebra не понимает.
export function conicCommand(k, digits = 12) {
  const t = [];
  const put = (v, what) => {
    if (!Number.isFinite(v) || Math.abs(v) < 1e-12) return;
    t.push(`${v > 0 && t.length ? '+' : ''}${v.toPrecision(digits)}${what}`);
  };
  put(k.xx, ' x^2'); put(k.xy, ' x y'); put(k.yy, ' y^2');
  put(k.x, ' x'); put(k.y, ' y'); put(k.one, '');
  return `${t.join(' ') || '0'} = 0`;
}

// Что это за кривая — по вещественным коэффициентам.
export function conicKind(k, tol = 1e-9) {
  const scale = Math.max(Math.abs(k.xx), Math.abs(k.xy), Math.abs(k.yy),
                         Math.abs(k.x), Math.abs(k.y), Math.abs(k.one), 1e-300);
  const small = v => Math.abs(v) <= tol * scale;
  if (small(k.xx) && small(k.xy) && small(k.yy)) {
    return (small(k.x) && small(k.y)) ? 'пусто' : 'прямая';
  }
  if (small(k.xy) && Math.abs(k.xx - k.yy) <= tol * scale) return 'окружность';
  const disc = k.xy * k.xy - 4 * k.xx * k.yy;
  if (small(disc)) return 'парабола';
  return disc < 0 ? 'эллипс' : 'гипербола';
}


// ---- кривая ЛЮБОГО порядка --------------------------------------------------
//
// Коника — частный случай, но рисовать надо и остальные: пользователь вправе
// увидеть, что у него получилось, даже если работать с этим дальше нельзя.
//
// Подставляем z = x + iy, z̄ = x − iy и раскрываем: каждый одночлен zᵖ z̄ᵠ даёт
// свой вклад в коэффициенты при xᵐ yⁿ. Дальше — та же проверка на
// вещественность, что и у коники: уравнение обязано быть пропорционально
// вещественному, иначе это не кривая.

const mul = (u, v) => ({ re: u.re * v.re - u.im * v.im, im: u.re * v.im + u.im * v.re });
const add = (u, v) => ({ re: u.re + v.re, im: u.im + v.im });

// (x + iy)^p (x − iy)^q как таблица одночленов: ключ «m,n» → комплексный вес.
function expand(p, q) {
  let cur = new Map([['0,0', { re: 1, im: 0 }]]);
  const times = (sign) => {
    const next = new Map();
    for (const [key, c] of cur) {
      const [m, n] = key.split(',').map(Number);
      const kx = `${m + 1},${n}`;
      next.set(kx, add(next.get(kx) ?? { re: 0, im: 0 }, c));
      const ky = `${m},${n + 1}`;
      next.set(ky, add(next.get(ky) ?? { re: 0, im: 0 },
        mul(c, { re: 0, im: sign })));
    }
    cur = next;
  };
  for (let t = 0; t < p; t++) times(1);
  for (let t = 0; t < q; t++) times(-1);
  return cur;
}

// Вещественный многочлен от x, y по разложению значения в степени (z, z̄).
export function realPoly(powers, evalAt, tol = 1e-7) {
  const acc = new Map();
  for (const [key, coeff] of powers) {
    const [p, q] = key.split(',').map(Number);
    const c = evalAt(coeff);
    if (!Number.isFinite(c.re) || !Number.isFinite(c.im)) return null;
    for (const [mn, w] of expand(p, q)) {
      const term = mul(c, w);
      acc.set(mn, add(acc.get(mn) ?? { re: 0, im: 0 }, term));
    }
  }
  const all = [...acc.values()];
  const abs = z => Math.hypot(z.re, z.im);
  const scale = Math.max(...all.map(abs), 0);
  if (!(scale > 0)) return null;
  const lead = all.find(z => abs(z) > tol * scale);
  const n = abs(lead);
  const phase = { re: lead.re / n, im: -lead.im / n };
  const out = new Map();
  for (const [mn, c] of acc) {
    const v = mul(c, phase);
    if (Math.abs(v.im) > tol * scale) return null;      // не вещественная кривая
    if (Math.abs(v.re) > 1e-12 * scale) out.set(mn, v.re);
  }
  return out.size ? out : null;
}

// Порядок кривой.
export function orderOf(coeffs) {
  let d = 0;
  for (const key of coeffs.keys()) {
    const [m, n] = key.split(',').map(Number);
    d = Math.max(d, m + n);
  }
  return d;
}

// Перенос в координаты чертежа: x = (X − ox)/r, y = (Y − oy)/r.
export function denormPoly(coeffs, ox, oy, r) {
  const s = 1 / r;
  const binom = (k) => {
    const row = [1];
    for (let t = 1; t <= k; t++) row.push(row[t - 1] * (k - t + 1) / t);
    return row;
  };
  const out = new Map();
  for (const [key, c] of coeffs) {
    const [m, n] = key.split(',').map(Number);
    const bx = binom(m), by = binom(n);
    for (let a = 0; a <= m; a++) {
      const wx = bx[a] * Math.pow(s, a) * Math.pow(-ox * s, m - a);
      for (let b = 0; b <= n; b++) {
        const wy = by[b] * Math.pow(s, b) * Math.pow(-oy * s, n - b);
        const k2 = `${a},${b}`;
        out.set(k2, (out.get(k2) ?? 0) + c * wx * wy);
      }
    }
  }
  for (const [k2, v] of [...out]) if (Math.abs(v) < 1e-13) out.delete(k2);
  return out;
}

// Строка уравнения для GeoGebra.
export function polyCommand(coeffs, digits = 12) {
  const parts = [];
  const keys = [...coeffs.keys()].sort((u, v) => {
    const [a, b] = u.split(',').map(Number), [c, d] = v.split(',').map(Number);
    return (c + d) - (a + b) || c - a;
  });
  for (const key of keys) {
    const [m, n] = key.split(',').map(Number);
    const v = coeffs.get(key);
    if (!Number.isFinite(v) || Math.abs(v) < 1e-13) continue;
    let t = `${v > 0 && parts.length ? '+' : ''}${v.toPrecision(digits)}`;
    if (m) t += m === 1 ? ' x' : ` x^${m}`;
    if (n) t += n === 1 ? ' y' : ` y^${n}`;
    parts.push(t);
  }
  return `${parts.join(' ') || '0'} = 0`;
}


// ---- обратный ход: уравнение GeoGebra → наши координаты ---------------------
//
// У встроенного локуса уравнения нет: это путь из точек. Уравнение даёт команда
// LocusEquation — неявной кривой, — и вот её-то строку и разбираем. Числа там
// уже приближённые, и точными они не станут; зато это настоящее уравнение той
// самой кривой, а не пересказ.

// Надстрочные цифры GeoGebra печатает Unicode: x³, y².
const SUP = { '\u2070': 0, '\u00b9': 1, '\u00b2': 2, '\u00b3': 3, '\u2074': 4,
              '\u2075': 5, '\u2076': 6, '\u2077': 7, '\u2078': 8, '\u2079': 9 };

// «1.99x³ + 1.99x y² - 1 = 0» → таблица одночленов.
// ПРАВАЯ ЧАСТЬ ПЕРЕНОСИТСЯ, а не отвергается: GeoGebra печатает уравнение как
// придётся — «… + 138921571159105y = -141310509793742», — и отказываться от
// такого значит отказываться от половины настоящих локусов.
export function parseImplicit(text) {
  let body = String(text ?? '');
  const colon = body.indexOf(':');
  if (colon >= 0) body = body.slice(colon + 1);
  const eq = body.indexOf('=');
  let right = null;
  if (eq >= 0) {
    right = body.slice(eq + 1);
    body = body.slice(0, eq);
  }
  const left = parseSide(body);
  if (!left) return null;
  if (right !== null && right.trim() && right.trim() !== '0') {
    const r = parseSide(right);
    if (!r) return null;
    for (const [k, v] of r) left.set(k, (left.get(k) ?? 0) - v);
  }
  for (const [k, v] of [...left]) if (Math.abs(v) < 1e-13) left.delete(k);
  return left.size ? left : null;
}

// Одна часть уравнения: сумма одночленов вида «коэффициент xᵐ yⁿ».
function parseSide(text) {
  let body = String(text ?? '').replace(/\s+/g, '').replace(/\*/g, '');
  if (!body) return null;
  const out = new Map();
  // Разбиваем по знакам верхнего уровня — скобок в таком уравнении не бывает.
  if (/[()]/.test(body)) return null;
  const pieces = body.replace(/-/g, '+-').split('+').filter(Boolean);
  for (const piece of pieces) {
    let rest = piece;
    let sign = 1;
    while (rest.startsWith('-')) { sign = -sign; rest = rest.slice(1); }
    const num = rest.match(/^\d*\.?\d*(?:[eE][+-]?\d+)?/)?.[0] ?? '';
    rest = rest.slice(num.length);
    let c = num === '' ? 1 : Number(num);
    if (!Number.isFinite(c)) return null;
    c *= sign;
    let m = 0, n = 0;
    while (rest) {
      const v = rest[0];
      if (v !== 'x' && v !== 'y') return null;
      rest = rest.slice(1);
      let d = 1;
      if (rest.startsWith('^')) {
        const k = rest.slice(1).match(/^\d+/)?.[0];
        if (!k) return null;
        d = Number(k); rest = rest.slice(1 + k.length);
      } else if (SUP[rest[0]] !== undefined) {
        d = 0;
        while (SUP[rest[0]] !== undefined) { d = d * 10 + SUP[rest[0]]; rest = rest.slice(1); }
      }
      if (v === 'x') m += d; else n += d;
    }
    const key = `${m},${n}`;
    out.set(key, (out.get(key) ?? 0) + c);
  }
  return out.size ? out : null;
}

// Обратно к нормированным координатам: X = ox + r·x, Y = oy + r·y.
export function normPoly(coeffs, ox, oy, r) {
  const binom = k => {
    const row = [1];
    for (let t = 1; t <= k; t++) row.push(row[t - 1] * (k - t + 1) / t);
    return row;
  };
  const out = new Map();
  for (const [key, c] of coeffs) {
    const [m, n] = key.split(',').map(Number);
    const bx = binom(m), by = binom(n);
    for (let a = 0; a <= m; a++) {
      const wx = bx[a] * Math.pow(r, a) * Math.pow(ox, m - a);
      for (let b = 0; b <= n; b++) {
        const wy = by[b] * Math.pow(r, b) * Math.pow(oy, n - b);
        const k2 = `${a},${b}`;
        out.set(k2, (out.get(k2) ?? 0) + c * wx * wy);
      }
    }
  }
  for (const [k2, v] of [...out]) if (Math.abs(v) < 1e-13) out.delete(k2);
  return out;
}

// Вещественный многочлен от x, y — в запись через z и z̄.
//
// x = (z + z̄)/2, y = (z − z̄)/(2i). Коэффициенты выходят комплексные, и это
// правильно: у вещественной кривой они сопряжены крест-накрест.
export function toZBar(coeffs, digits = 4) {
  const acc = new Map();
  const addTo = (key, re, im) => {
    const cur = acc.get(key) ?? { re: 0, im: 0 };
    acc.set(key, { re: cur.re + re, im: cur.im + im });
  };
  const mulC = (u, v) => ({ re: u.re * v.re - u.im * v.im, im: u.re * v.im + u.im * v.re });
  for (const [key, c] of coeffs) {
    const [m, n] = key.split(',').map(Number);
    // (z + z̄)/2 в степени m и (z − z̄)/(2i) в степени n — раскрываем биномом.
    let cur = new Map([['0,0', { re: c, im: 0 }]]);
    const times = (wz, wzc) => {
      const next = new Map();
      for (const [k2, u] of cur) {
        const [p, q] = k2.split(',').map(Number);
        const a = mulC(u, wz), b = mulC(u, wzc);
        const ka = `${p + 1},${q}`, kb = `${p},${q + 1}`;
        const pa = next.get(ka) ?? { re: 0, im: 0 };
        next.set(ka, { re: pa.re + a.re, im: pa.im + a.im });
        const pb = next.get(kb) ?? { re: 0, im: 0 };
        next.set(kb, { re: pb.re + b.re, im: pb.im + b.im });
      }
      cur = next;
    };
    for (let t = 0; t < m; t++) times({ re: 0.5, im: 0 }, { re: 0.5, im: 0 });
    for (let t = 0; t < n; t++) times({ re: 0, im: -0.5 }, { re: 0, im: 0.5 });
    for (const [k2, u] of cur) addTo(k2, u.re, u.im);
  }
  const parts = [];
  const keys = [...acc.keys()].sort((u, v) => {
    const [a, b] = u.split(',').map(Number), [c, d] = v.split(',').map(Number);
    return (c + d) - (a + b) || c - a;
  });
  // Уравнение задано с точностью до множителя, и GeoGebra печатает его в целых:
  // «22898000000000x⁴ + …». Читать такое нельзя, а множитель ничего не значит —
  // делим на модуль старшего коэффициента. Именно на МОДУЛЬ: делить на само
  // комплексное число нельзя, иначе сломается сопряжённая симметрия, по которой
  // и видно, что кривая вещественная.
  let big = 0;
  for (const u of acc.values()) big = Math.max(big, Math.hypot(u.re, u.im));
  const scale = big > 0 ? 1 / big : 1;
  const near0 = 1e-10;
  for (const key of keys) {
    const [p, q] = key.split(',').map(Number);
    const raw = acc.get(key);
    const u = { re: raw.re * scale, im: raw.im * scale };
    if (Math.abs(u.re) < near0 && Math.abs(u.im) < near0) continue;
    const short = v => Number(v.toPrecision(digits));
    let c = Math.abs(u.im) < near0 ? `${short(u.re)}`
      : Math.abs(u.re) < near0 ? `${short(u.im)}i`
      : `(${short(u.re)}${u.im > 0 ? '+' : ''}${short(u.im)}i)`;
    let t = '';
    if (p) t += p === 1 ? 'z' : `z^${p}`;
    if (q) t += q === 1 ? 'z̄' : `z̄^${q}`;
    parts.push(`${parts.length && !c.startsWith('-') ? '+ ' : ''}${c}${t ? ' ' + t : ''}`);
  }
  return `${parts.join(' ') || '0'} = 0`;
}
