// Численный слой: обычные комплексные числа с плавающей точкой.
//
// Нужен для двух вещей, которые символьно не решаются в принципе:
//   1) понять, какому из двух корней квадратного уравнения соответствует
//      конкретная точка, которую GeoGebra назвала Intersect[f, k, 2];
//   2) сверять символьный ответ с настоящим чертежом.
//
// Тонкость: A, B, C на экране НЕ лежат на единичной окружности с центром в
// нуле — движок так только считает. Поэтому сравнивать надо в нормированных
// координатах z ↦ (z − O)/R, где O и R — численные центр и радиус описанной.
// Это подобие, а все построения (середина, пересечение, отражение, проекция)
// под подобиями сохраняются, так что символьное значение любой построенной
// точки совпадает с нормированной координатой её настоящего положения.

export const C = {
  of: (re, im) => ({ re, im }),
  add: (x, y) => ({ re: x.re + y.re, im: x.im + y.im }),
  sub: (x, y) => ({ re: x.re - y.re, im: x.im - y.im }),
  mul: (x, y) => ({ re: x.re * y.re - x.im * y.im, im: x.re * y.im + x.im * y.re }),
  conj: x => ({ re: x.re, im: -x.im }),
  scale: (x, k) => ({ re: x.re * k, im: x.im * k }),
  abs: x => Math.hypot(x.re, x.im),
  div(x, y) {
    const d = y.re * y.re + y.im * y.im;
    if (d === 0) return { re: NaN, im: NaN };
    return { re: (x.re * y.re + x.im * y.im) / d, im: (x.im * y.re - x.re * y.im) / d };
  },
  isFinite: x => Number.isFinite(x.re) && Number.isFinite(x.im),
};

// Центр описанной окружности трёх точек. Возвращает null для вырожденного
// (коллинеарного) случая — тогда нормировать нечем.
export function circumcenterNumeric(p, q, r) {
  const cp = C.conj(p), cq = C.conj(q), cr = C.conj(r);
  // та же формула, что в formulas.js: |z|²-веса на разностях самих точек,
  // знаменатель — на сопряжённых. Перепутать местами = получить сопряжение
  // центра, что здесь уже случалось.
  const term = (z, cz, u, v) => C.mul(C.mul(z, cz), C.sub(u, v));
  const num = C.add(C.add(term(p, cp, q, r), term(q, cq, r, p)), term(r, cr, p, q));
  const den = C.add(C.add(C.mul(cp, C.sub(q, r)), C.mul(cq, C.sub(r, p))), C.mul(cr, C.sub(p, q)));
  if (C.abs(den) < 1e-12) return null;
  const o = C.div(num, den);
  return C.isFinite(o) ? o : null;
}

// Система координат движка на чертеже: центр описанной и её радиус.
//
// Обратное отображение нужно там, где сравнивать приходится не с точкой, а с
// ОБЪЕКТОМ чертежа: у прямой GeoGebra отдаёт коэффициенты a·x + b·y + c = 0 в
// координатах экрана, и подставлять в них символьный ответ можно только вернув
// его на чертёж.
export function circumFrame(pa, pb, pc) {
  const o = circumcenterNumeric(pa, pb, pc);
  if (!o) return null;
  const radius = C.abs(C.sub(pa, o));
  if (!(radius > 1e-9)) return null;
  return {
    o,
    radius,
    norm: z => C.scale(C.sub(z, o), 1 / radius),
    denorm: z => C.add(o, C.scale(z, radius)),
  };
}

// Отображение чертежа в ту систему координат, в которой считает движок.
export function makeNormalizer(pa, pb, pc) {
  return circumFrame(pa, pb, pc)?.norm ?? null;
}

// Расстояние от точки до прямой чертежа. Прямая приходит от GeoGebra тройкой
// коэффициентов a·x + b·y + c = 0 (getXcoord/getYcoord/getZcoord у GeoLine —
// это именно они, проверено в живом апплете), и тройка задана с точностью до
// множителя, поэтому нормируем на длину нормали.
export function distanceToLine({ a, b, c }, z) {
  const scale = Math.hypot(a, b);
  if (!(scale > 0) || !C.isFinite(z)) return Infinity;
  return Math.abs(a * z.re + b * z.im + c) / scale;
}

// Какой из кандидатов ближе к цели. Возвращает индекс или -1, если ни один
// не посчитался.
export function nearestIndex(candidates, target) {
  let best = -1;
  let bestDist = Infinity;
  candidates.forEach((z, i) => {
    if (!C.isFinite(z)) return;
    const d = C.abs(C.sub(z, target));
    if (d < bestDist) { bestDist = d; best = i; }
  });
  return best;
}
