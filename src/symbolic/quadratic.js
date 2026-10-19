import { CircleEq } from './circle.js';
import { LineEq } from './line.js';
import { QuadraticExt } from './quadratic-ext.js';

// Квадратные уравнения над полем рациональных функций от образующих.
//
// Общего механизма радикалов здесь нет и не планируется: решить, извлекается ли
// корень из многочлена от нескольких переменных, — задача того же класса, что и
// полный полиномиальный GCD, от которого в этом проекте сознательно отказались.
//
// Зато решается всё, что решается БЕЗ радикалов, а таких случаев в планиметрии
// большинство:
//   * старший коэффициент нулевой — уравнение на самом деле линейное;
//   * дискриминант тождественно нулевой — касание, двойной корень;
//   * один корень уже известен (медиана и описанная имеют общую точку a) —
//     второй берётся по Виету.
//
// По Виету используется СУММА, а не произведение: известный корень вполне может
// оказаться нулём — у нас там центр описанной окружности.
export function solveQuadratic(A, B, C, knownPoints = []) {
  if (A.isZero()) {
    if (B.isZero()) return { kind: 'degenerate', roots: [] };
    return { kind: 'linear', roots: [C.div(B).neg()] };
  }
  // Известный корень ищем ПЕРВЫМ: это несколько подстановок, тогда как
  // дискриминант — произведение больших выражений. На системах из командной
  // строки, где в кольце десяток образующих, разница была секунды против
  // миллисекунд. Касание при этом не теряется: у него оба корня совпадают.
  const sum = B.div(A).neg();
  for (const z0 of knownPoints) {
    if (A.mul(z0).mul(z0).add(B.mul(z0)).add(C).isZero()) {
      const other = sum.sub(z0);
      if (other.equals(z0)) return { kind: 'tangent', roots: [z0] };
      return { kind: 'vieta', roots: [z0, other], known: z0 };
    }
  }

  const D = B.mul(B).sub(A.mul(C).mul(4n));
  if (D.isZero()) return { kind: 'tangent', roots: [B.div(A.mul(2n)).neg()] };
  return { kind: 'irrational', roots: [] };
}

// Пересечение прямой z + β·z̄ + γ = 0 с окружностью (z − o)(z̄ − ō) = r².
//
// Из уравнения прямой z̄ = −(z + γ)/β; подставляем в окружность и получаем
//     z² + (k − o)·z + (r²β − o·k) = 0,   где k = γ + ō·β.
// Для хорды единичной окружности через p, q (β = pq, γ = −(p+q)) это
// вырождается в z² − (p+q)z + pq = 0, то есть ровно в корни p и q.
export function lineMeetsCircle(line, circle, knownPoints = []) {
  const ring = line.beta.ring;
  const o = circle.center;
  const k = line.gamma.add(o.conjugate().mul(line.beta));
  const A = ring.one();
  const B = k.sub(o);

  // Известный корень распознаём ГЕОМЕТРИЧЕСКИ, а не подстановкой в уравнение:
  // точка является корнем ровно тогда, когда лежит и на прямой, и на
  // окружности — само уравнение подстановкой одного в другое и получено.
  //
  // Разница не косметическая. Подстановка требует свободного члена
  // C = r²β − o·k, а он — самое дорогое выражение всей задачи, тогда как по
  // Виету (z₂ = −B/A − z₁) не нужен вовсе. На пересечении описанных
  // окружностей EBG и DCG, где D, E, G взяты на сторонах треугольника, сам
  // ответ весит 32 члена и считается за секунды, а вот C по дороге съедал всю
  // память, и вкладка вставала намертво. Считать C только тогда, когда без
  // него правда не обойтись, — и есть разница между «зависло» и «готово».
  for (const z0 of knownPoints) {
    if (circle.contains(z0) && line.contains(z0)) {
      const other = B.neg().sub(z0);
      if (other.equals(z0)) return { kind: 'tangent', roots: [z0] };
      return { kind: 'vieta', roots: [z0, other], known: z0 };
    }
  }

  const C = circle.r2.mul(line.beta).sub(o.mul(k));
  return solveQuadratic(A, B, C);
}

// Пересечение двух окружностей отдельного механизма не требует: разность их
// развёрнутых уравнений — радикальная ось, обычная прямая (члены z z̄
// сокращаются), дальше это пересечение прямой с окружностью.
export function circlesMeet(c1, c2, knownPoints = []) {
  return lineMeetsCircle(CircleEq.radicalAxis(c1, c2), c1, knownPoints);
}

// ---- присоединение корня ---------------------------------------------------
//
// Сюда попадают ровно те случаи, где раньше движок капитулировал: среди
// построенных точек корня нет, касания нет, уравнение честно квадратное.
// Вместо «нужны радикалы» присоединяем корень к полю (см. quadratic-ext.js).
//
// Сначала — проверка на разложимость. Дискриминант вполне может оказаться
// полным квадратом: тогда корни рациональны, расширение не нужно и заводить его
// было бы вредно (все последующие сравнения стали бы дороже на ровном месте).
// Извлечение точного корня уже есть — то же самое, что считает центры гомотетии.
export function lineMeetsCircleExtended(line, circle, knownPoints = [], name = 'x') {
  const direct = lineMeetsCircle(line, circle, knownPoints);
  if (direct.kind !== 'irrational') return direct;

  const ring = line.beta.ring;
  const o = circle.center;
  const k = line.gamma.add(o.conjugate().mul(line.beta));
  const B = k.sub(o);
  const C = circle.r2.mul(line.beta).sub(o.mul(k));

  // z² + Bz + C = 0, поэтому по Виету S = −B, Q = C.
  const S = B.neg();
  const Q = C;

  const disc = S.mul(S).sub(Q.mul(4n));
  const rootOfDisc = disc.sqrt();
  if (rootOfDisc) {
    const first = S.add(rootOfDisc).div(2n);
    return { kind: 'split', roots: [first, S.sub(first)] };
  }

  const ext = new QuadraticExt(ring, S, Q, name).setCircleRule(circle);
  return { kind: 'extended', ext, roots: [ext.root(), ext.other()] };
}

export function liftCircle(ext, circle) {
  return new CircleEq(ext.lift(circle.center), ext.lift(circle.r2));
}

// Расширение по готовому рецепту «x² − Sx + Q = 0».
//
// Нужно системам из командной строки: там корень находят в локальном кольце, а
// присоединять его надо уже после подстановки вершин — в том кольце, где живут
// настоящие выражения (см. solveWithQuadratic).
// Кольцо берётся из самих S и Q: отдельным аргументом его пришлось бы
// согласовывать, а ошибка согласования тут самая дорогая — расширение не над
// тем кольцом ломается не сразу, а на первом же сравнении.
export function adjoinBySumAndProduct(S, Q, name = 'x') {
  const ring = S.ring;
  const root = S.mul(S).sub(Q.mul(4n)).sqrt();
  if (root) {
    const first = S.add(root).div(2n);
    return { kind: 'split', roots: [first, S.sub(first)] };
  }
  const ext = new QuadraticExt(ring, S, Q, name);
  return { kind: 'extended', ext, roots: [ext.root(), ext.other()] };
}
