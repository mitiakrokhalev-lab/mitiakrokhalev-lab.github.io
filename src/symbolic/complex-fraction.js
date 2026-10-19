import { Fraction, ZERO_Q } from './fraction.js';

// Exact Gaussian rationals: re + im*i, both exact Fractions.
export class CFrac {
  constructor(re = 0n, im = 0n) {
    this.re = Fraction.from(re);
    this.im = Fraction.from(im);
  }
  static from(x) { return x instanceof CFrac ? x : new CFrac(x, 0n); }
  // Мнимая часть почти всегда нулевая: комплексные коэффициенты появляются
  // только там, где в формулу входит i. Короткий путь экономит три умножения
  // дробей из четырёх.
  add(o) {
    o = CFrac.from(o);
    if (this.im.isZero() && o.im.isZero()) return new CFrac(this.re.add(o.re), ZERO_Q);
    return new CFrac(this.re.add(o.re), this.im.add(o.im));
  }
  sub(o) { o = CFrac.from(o); return new CFrac(this.re.sub(o.re), this.im.sub(o.im)); }
  mul(o) {
    o = CFrac.from(o);
    if (this.im.isZero() && o.im.isZero()) return new CFrac(this.re.mul(o.re), ZERO_Q);
    return new CFrac(
      this.re.mul(o.re).sub(this.im.mul(o.im)),
      this.re.mul(o.im).add(this.im.mul(o.re))
    );
  }
  div(o) {
    o = CFrac.from(o);
    const denom = o.re.mul(o.re).add(o.im.mul(o.im));
    if (denom.isZero()) throw new Error('CFrac: division by zero');
    return new CFrac(
      this.re.mul(o.re).add(this.im.mul(o.im)).div(denom),
      this.im.mul(o.re).sub(this.re.mul(o.im)).div(denom)
    );
  }
  neg() { return new CFrac(this.re.neg(), this.im.neg()); }
  conj() { return new CFrac(this.re, this.im.neg()); }
  isZero() { return this.re.isZero() && this.im.isZero(); }
  isOne() { return this.re.equals(1n) && this.im.isZero(); }
  equals(o) { o = CFrac.from(o); return this.re.equals(o.re) && this.im.equals(o.im); }
  toNumber() { return { re: this.re.toNumber(), im: this.im.toNumber() }; }
  toString() {
    // единичный коэффициент при i не печатаем: «1-i», а не «1-1i»
    const imPart = f => (f.d === 1n && (f.n === 1n || f.n === -1n) ? '' : f.toString()) + 'i';
    if (this.im.isZero()) return this.re.toString();
    if (this.re.isZero()) return (this.im.n < 0n ? '-' : '') + imPart(this.im.n < 0n ? this.im.neg() : this.im);
    const negImag = this.im.n < 0n;
    const imAbs = negImag ? this.im.neg() : this.im;
    return `${this.re.toString()}${negImag ? '-' : '+'}${imPart(imAbs)}`;
  }
}

export const ZERO = new CFrac(0n, 0n);
export const ONE = new CFrac(1n, 0n);
export const I = new CFrac(0n, 1n);
