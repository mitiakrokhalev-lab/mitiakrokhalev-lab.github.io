import { LineEq } from './line.js';

// Символьное уравнение коники в комплексных координатах.
//
//     A z² + B z z̄ + C z̄² + D z + E z̄ + F = 0
//
// Шесть коэффициентов, то есть пять степеней свободы после умножения на
// константу — ровно столько, сколько точек конику задаёт.
//
// Вещественность кривой означает C = conj(A), E = conj(D) и вещественные B, F;
// но НАВЯЗЫВАТЬ это нельзя: коника, полученная через пять точек, выходит с
// точностью до множителя, и множитель этот бывает невещественным. Всё, чем мы
// пользуемся — принадлежность, поляра, центр, — от множителя не зависит,
// поэтому нормировку не трогаем вовсе.
export class ConicEq {
  constructor(a, b, c, d, e, f) {
    this.a = a; this.b = b; this.c = c; this.d = d; this.e = e; this.f = f;
  }

  get ring() { return this.a.ring; }

  coeffs() { return [this.a, this.b, this.c, this.d, this.e, this.f]; }

  // Коника задана с точностью до множителя, поэтому его можно и нужно убрать:
  // делим на первый ненулевой коэффициент. Иначе через пять точек описанной
  // выходит не «z z̄ = 1», а та же кривая, помноженная на произведение всех
  // разностей — читать это нельзя, а смысла в множителе никакого.
  normalized() {
    const first = this.coeffs().find(k => !k.isZero());
    if (!first || first.equals(this.ring.one())) return this;
    return new ConicEq(...this.coeffs().map(k => k.div(first)));
  }

  // Строка точки в базисе (z², z z̄, z̄², z, z̄, 1). Через неё выражается всё
  // остальное: и подстановка точки, и коника по пяти точкам.
  static row(z) {
    const zc = z.conjugate();
    return [z.mul(z), z.mul(zc), zc.mul(zc), z, zc, z.ring.one()];
  }

  at(z) {
    const row = ConicEq.row(z);
    return this.coeffs().reduce((acc, k, i) => acc.add(k.mul(row[i])), this.ring.zero());
  }

  contains(z) { return this.at(z).isZero(); }

  // Поляра точки w: из билинейной формы X^T M W, где X = (z, z̄, 1).
  // Касательная в точке коники — тот же самый объект, отдельной формулы нет.
  polar(w) {
    const wc = w.conjugate();
    const two = 2n;
    // Коэффициенты при z, z̄ и свободный член.
    const az = this.a.mul(w).mul(two).add(this.b.mul(wc)).add(this.d);
    const azc = this.b.mul(w).add(this.c.mul(wc).mul(two)).add(this.e);
    const c0 = this.d.mul(w).add(this.e.mul(wc)).add(this.f.mul(two));
    if (az.isZero()) return null;      // поляра вырождена (точка в центре)
    return new LineEq(azc.div(az), c0.div(az));
  }

  tangentAt(z) { return this.polar(z); }

  // Центр: точка, где обе производные обращаются в ноль, то есть решение
  // 2A z + B z̄ + D = 0,  B z + 2C z̄ + E = 0.
  // У параболы определитель нулевой — центра нет, и это не ошибка.
  centre() {
    const two = 2n;
    const det = this.a.mul(this.c).mul(4n).sub(this.b.mul(this.b));
    if (det.isZero()) return null;
    // z = (B·E − 2C·D) / (4AC − B²)
    return this.b.mul(this.e).sub(this.c.mul(this.d).mul(two)).div(det);
  }

  // Коника через пять точек.
  //
  // Определитель 6×6 из строки переменной точки и пяти строк данных обращается
  // в ноль ровно на конике через них. Раскладывая его по первой строке,
  // получаем коэффициенты — это миноры 5×5 со знаками.
  static throughFivePoints(points) {
    if (points.length !== 5) throw new Error('конике нужно ровно пять точек');
    const rows = points.map(ConicEq.row);
    const ring = points[0].ring;
    const coeffs = [];
    for (let col = 0; col < 6; col++) {
      const minor = rows.map(r => r.filter((_, j) => j !== col));
      const value = det(minor, ring);
      coeffs.push(col % 2 === 0 ? value : value.neg());
    }
    if (coeffs.every(k => k.isZero())) return null;   // точки не задают конику
    return new ConicEq(...coeffs).normalized();
  }

  // Шесть точек на одной конике: определитель 6×6 из их строк равен нулю.
  // Через пять точек конику проводить не нужно — ответ и так здесь.
  static conconic(points) {
    if (points.length !== 6) throw new Error('проверка требует ровно шести точек');
    return det(points.map(ConicEq.row), points[0].ring).isZero();
  }

  // Парабола по фокусу и директрисе: |z − f|² = (расстояние до прямой)².
  //
  // У нормированной прямой (|β| = 1) невязка r = z + β z̄ + γ, а расстояние —
  // |r|/2. Возведение в квадрат радикалы убирает, поэтому уравнение выходит
  // рациональным без всяких расширений.
  static parabola(focus, line) {
    const beta = line.beta, gamma = line.gamma;
    const bc = beta.conjugate(), gc = gamma.conjugate();
    const fc = focus.conjugate();
    return new ConicEq(
      bc.neg(),
      focus.ring.constant(2n),
      beta.neg(),
      fc.mul(4n).neg().sub(gc.add(gamma.mul(bc))),
      focus.mul(4n).neg().sub(beta.mul(gc).add(gamma)),
      focus.mul(fc).mul(4n).sub(gamma.mul(gc)),
    );
  }

  // Эллипс или гипербола по двум фокусам и точке на кривой.
  //
  // Через 2a = |PF₁| ± |PF₂| писать нельзя — это радикалы. Но если обозначить
  // u = |z−f₁|², v = |z−f₂|², то разность u − v ЛИНЕЙНА, и из |z−f₁| = a +
  // (u−v)/4a возведением в квадрат получается
  //
  //     16a²·u − 16a⁴ − 8a²·(u−v) − (u−v)² = 0,
  //
  // где рационально всё, кроме самого a². А a² = (d₁² + d₂² ± 2·d₁d₂)/4, и
  // единственная иррациональность — d₁d₂, квадрат которого рационален. Знак
  // различает эллипс и гиперболу; отсюда же и «одна из двух» — коника через
  // фокусы и точку задаётся парой.
  // Квадрат большой полуоси по фокусам и точке на кривой.
  //
  // 2a = |PF₁| + |PF₂| (эллипс), значит 4a² = u + v + 2√(uv), где u и v —
  // квадраты расстояний. Рационально всё, кроме √(uv); когда и он рационален,
  // коника выражается через a, b, c без всяких расширений, а когда нет —
  // честный отказ, как у центров гомотетии.
  //
  // Гипербола отличается знаком: 2a = ||PF₁| − |PF₂||. Через фокусы и точку
  // проходят ОБЕ кривые, и какая нужна — вопрос не алгебры, а чертежа.
  static squaredAxis(f1, f2, through, hyperbola = false) {
    const du = through.sub(f1), dv = through.sub(f2);
    const u = du.mul(du.conjugate()), v = dv.mul(dv.conjugate());
    const t = u.mul(v).sqrt();
    if (!t) return null;
    const twice = t.mul(2n);
    return { value: (hyperbola ? u.add(v).sub(twice) : u.add(v).add(twice)).div(4n),
             hyperbola };
  }

  static byFociAndSquaredAxis(f1, f2, a2) {
    const ring = f1.ring;
    const u = z => z.sub(f1).mul(z.sub(f1).conjugate());
    const v = z => z.sub(f2).mul(z.sub(f2).conjugate());
    // Коэффициенты собираем подстановкой символической точки нельзя — поэтому
    // раскрываем руками: u и v квадратичны, u − v линейна.
    const f1c = f1.conjugate(), f2c = f2.conjugate();
    // u = z z̄ − f̄₁ z − f₁ z̄ + f₁f̄₁,  v = z z̄ − f̄₂ z − f₂ z̄ + f₂f̄₂
    // s = u − v = (f̄₂ − f̄₁) z + (f₂ − f₁) z̄ + (f₁f̄₁ − f₂f̄₂)
    const sz = f2c.sub(f1c), szc = f2.sub(f1), s0 = f1.mul(f1c).sub(f2.mul(f2c));
    const eight = a2.mul(8n), sixteen = a2.mul(16n);
    // 16a²·u: коэффициенты (0, 16a², 0, −16a²f̄₁, −16a²f₁, 16a²f₁f̄₁)
    // −8a²·s:              (0, 0, 0, −8a²·sz, −8a²·szc, −8a²·s0)
    // −s²:  s² = sz²z² + 2·sz·szc·zz̄ + szc²z̄² + 2sz·s0·z + 2szc·s0·z̄ + s0²
    return new ConicEq(
      sz.mul(sz).neg(),
      sixteen.sub(sz.mul(szc).mul(2n)),
      szc.mul(szc).neg(),
      sixteen.mul(f1c).neg().sub(eight.mul(sz)).sub(sz.mul(s0).mul(2n)),
      sixteen.mul(f1).neg().sub(eight.mul(szc)).sub(szc.mul(s0).mul(2n)),
      sixteen.mul(f1).mul(f1c).sub(eight.mul(s0)).sub(s0.mul(s0)).sub(a2.mul(a2).mul(16n)),
    );
  }

  toString() { return this.#render(false); }
  toTex() { return this.#render(true); }

  #render(tex) {
    // Слэш обязан быть ДВОЙНЫМ: в строке JS «\\b» — служебный символ, а не начало
    // \\bar. С одинарным katex получал мусор и рисовал строку красным.
    const names = tex
      ? ['z^2', 'z \\bar{z}', '\\bar{z}^2', 'z', '\\bar{z}', '']
      : ['z²', 'z z̄', 'z̄²', 'z', 'z̄', ''];
    const parts = this.coeffs().map((k, i) => {
      if (k.isZero()) return null;
      const c = tex ? k.toTex() : k.toString();
      const wrap = tex ? `\\left(${c}\\right)` : `(${c})`;
      return names[i] ? `${wrap}${tex ? ' ' : '·'}${names[i]}` : wrap;
    }).filter(Boolean);
    return `${parts.join(' + ')} = 0`;
  }
}

// Определитель символьной матрицы разложением по первой строке. Пять на пять —
// сто двадцать слагаемых, для наших размеров этого достаточно.
export function det(m, ring) {
  const n = m.length;
  if (n === 1) return m[0][0];
  let acc = ring.zero();
  for (let col = 0; col < n; col++) {
    if (m[0][col].isZero()) continue;
    const minor = m.slice(1).map(r => r.filter((_, j) => j !== col));
    const part = m[0][col].mul(det(minor, ring));
    acc = col % 2 === 0 ? acc.add(part) : acc.sub(part);
  }
  return acc;
}
