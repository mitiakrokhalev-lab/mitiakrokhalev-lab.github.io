import { LineEq, canonicalSum, TEX_ZBAR, TEX_OPEN, TEX_CLOSE } from './line.js';
import { F } from './formulas.js';

// Символьное уравнение окружности.
//
// Храним центр o и КВАДРАТ радиуса r² — именно эта пара нужна всем, кто с
// окружностью работает (точка на ней, поляра, пересечения), и обе величины
// рациональны, тогда как сам радиус — нет.
//
//     (z − o)(z̄ − ō) = r²
//
// Развёрнутый вид, он же нужен для радикальной оси:
//
//     z z̄ + A z + Ā z̄ + C = 0,   A = −ō,  C = o ō − r²
//
// Коэффициент при z̄ обязан быть сопряжён коэффициенту при z, а C — веществен;
// это эрмитовость, она проверяется тестом.
export class CircleEq {
  constructor(center, r2) {
    this.center = center;
    this.r2 = r2;
  }

  get ring() { return this.center.ring; }

  static centerAndPoint(center, through) {
    const d = through.sub(center);
    return new CircleEq(center, d.mul(d.conjugate()));
  }

  // Циркуль: раствор берём по отрезку AB, ножку ставим в C.
  //
  // Радикал тут не нужен, хотя на первый взгляд нужен: расстояние |AB|
  // иррационально, но окружность хранится центром и КВАДРАТОМ радиуса, а
  // |AB|² = (B−A)·conj(B−A) — обычная рациональная функция. Именно поэтому
  // перенос раствора, который у Евклида и есть отдельная нетривиальная
  // конструкция, здесь стоит одну строку.
  static compass(from, to, center) {
    const d = to.sub(from);
    if (d.isZero()) throw new Error('циркуль: раствор нулевой — A и B совпали');
    return new CircleEq(center, d.mul(d.conjugate()));
  }

  // Окружность через три точки — центр описанной плюс любая из них.
  //
  // Вырожденный случай (три точки на одной прямой) формула центра встречает
  // делением на ноль, а в панели пользователю нужно человеческое объяснение.
  // Знаменатель этой формулы и есть определитель коллинеарности, поэтому
  // проверяем его отдельно; сопряжения точек к этому моменту уже посчитаны.
  static throughThreePoints(p, q, r) {
    const pc = p.conjugate(), qc = q.conjugate(), rc = r.conjugate();
    const det = pc.mul(q.sub(r)).add(qc.mul(r.sub(p))).add(rc.mul(p.sub(q)));
    if (det.isZero()) throw new Error('три точки на одной прямой — окружности через них нет');
    return CircleEq.centerAndPoint(F.circumcenter(p, q, r), p);
  }

  // Коэффициенты развёрнутого вида.
  coefA() { return this.center.conjugate().neg(); }
  coefC() { return this.center.mul(this.center.conjugate()).sub(this.r2); }

  // (z − o)(z̄ − ō) − r²; ноль ровно тогда, когда z на окружности.
  residual(z) {
    return z.sub(this.center).mul(z.sub(this.center).conjugate()).sub(this.r2);
  }

  contains(z) { return this.residual(z).isZero(); }

  equals(other) {
    return this.center.equals(other.center) && this.r2.equals(other.r2);
  }

  // Поляра точки p: (z − o)·conj(p − o) + (z̄ − ō)·(p − o) = 2r².
  // Если p лежит на окружности, это ровно касательная в p. Для единичной
  // окружности сводится к классике z + p²·z̄ = 2p.
  polarLine(p) {
    const dp = p.sub(this.center);
    const dpc = dp.conjugate();
    if (dpc.isZero()) throw new Error('поляра центра не определена');
    const beta = dp.div(dpc);
    const delta = this.r2.mul(2n)
      .add(this.center.mul(dpc))
      .add(this.center.conjugate().mul(dp))
      .div(dpc);
    return LineEq.fromBetaDelta(beta, delta);
  }

  // Инверсия относительно окружности: z ↦ o + r²/conj(z − o).
  // Рациональна — никаких радикалов, поэтому поддерживается наравне с
  // отражениями. Центр в себя не переходит: его образ бесконечно удалён.
  invert(z) {
    const d = z.sub(this.center);
    if (d.isZero()) throw new Error('инверсия центра не определена');
    return this.center.add(this.r2.div(d.conjugate()));
  }

  // Радикальная ось двух окружностей: разность их развёрнутых уравнений.
  // Члены z z̄ сокращаются, остаётся обычная прямая — поэтому пересечение двух
  // окружностей не требует отдельного механизма, оно сводится к пересечению
  // прямой с окружностью.
  static radicalAxis(c1, c2) {
    const d = c2.center.sub(c1.center);
    if (d.isZero()) throw new Error('концентрические окружности: радикальной оси нет');
    const dc = d.conjugate();
    // conj(o₂−o₁)·z + (o₂−o₁)·z̄ + (C₁−C₂) = 0, нормируем делением на conj(o₂−o₁)
    return new LineEq(d.div(dc), c1.coefC().sub(c2.coefC()).div(dc));
  }

  // Канонический вид z z̄ + A·z + Ā·z̄ + C = 0 — те же скобки, только раскрытые.
  // Коэффициент при z z̄ обязан остаться единицей, поэтому знаменатели здесь, в
  // отличие от прямой, не выносятся: иначе это была бы уже другая нормировка.
  toCanonical() {
    const A = this.coefA();
    const Ac = this.center.neg();          // сопряжение A, оно же −o
    const C = this.coefC();
    return {
      text: canonicalSum('z z̄', [[A, 'z'], [Ac, 'z̄'], [C, '']],
        r => r.toString(), '(', ')'),
      tex: canonicalSum(`z ${TEX_ZBAR}`, [[A, 'z'], [Ac, TEX_ZBAR], [C, '']],
        r => r.toTex(), TEX_OPEN, TEX_CLOSE),
    };
  }

  toString() { return this.#render(r => r.toString(), 'z̄', '(', ')'); }

  toTex() { return this.#render(r => r.toTex(), '\\bar{z}', '\\left(', '\\right)'); }

  #render(str, zbar, open, close) {
    const r2 = str(this.r2);
    if (this.center.isZero()) return `z ${zbar} = ${r2}`;
    const o = this.center.isSimple() ? str(this.center) : `${open}${str(this.center)}${close}`;
    const oc = this.center.conjugate();
    const ocs = oc.isSimple() ? str(oc) : `${open}${str(oc)}${close}`;
    return `(z − ${o})(${zbar} − ${ocs}) = ${r2}`;
  }
}
