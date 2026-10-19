import { checkComputeBudget } from './budget.js';
// Exact rational numbers (bigint-backed) so factor cancellation is never
// corrupted by floating point noise.

function gcd(a, b) {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  // Евклид по огромным целым — САМОЕ долгое место движка. Профиль на реальной
  // задаче (пересечение прямой через точку на касательной с описанной) показал
  // здесь 92% всего времени: 27 секунд из 29. Коэффициенты вырастают до тысяч
  // знаков, и один такой цикл идёт секундами.
  //
  // Без проверки ВНУТРИ него бюджет опаздывал на двадцать три секунды: он ведь
  // проверяется между операциями, а тут всё время уходит внутри одной. Часы
  // спрашиваем раз в шестнадцать шагов — на фоне деления многотысячезначных
  // чисел это не стоит ничего.
  let steps = 0;
  while (b) {
    if ((++steps & 15) === 0) checkComputeBudget();
    [a, b] = [b, a % b];
  }
  return a === 0n ? 1n : a;
}

export class Fraction {
  constructor(n, d = 1n) {
    n = typeof n === 'bigint' ? n : BigInt(n);
    d = typeof d === 'bigint' ? d : BigInt(d);
    // Подавляющее большинство коэффициентов целые, а сокращать целое на единицу
    // незачем: НОД двух bigint'ов — самая горячая операция во всём движке.
    if (d === 1n) { this.n = n; this.d = 1n; return; }
    if (d === 0n) throw new Error('Fraction: division by zero');
    if (d < 0n) { n = -n; d = -d; }
    const g = gcd(n, d);
    this.n = n / g;
    this.d = d / g;
  }
  static from(x) { return x instanceof Fraction ? x : new Fraction(x, 1n); }
  add(o) { o = Fraction.from(o); return new Fraction(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { o = Fraction.from(o); return new Fraction(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { o = Fraction.from(o); return new Fraction(this.n * o.n, this.d * o.d); }
  div(o) { o = Fraction.from(o); if (o.n === 0n) throw new Error('Fraction: division by zero'); return new Fraction(this.n * o.d, this.d * o.n); }
  neg() { return new Fraction(-this.n, this.d); }
  isZero() { return this.n === 0n; }
  isInt() { return this.d === 1n; }
  equals(o) { o = Fraction.from(o); return this.n === o.n && this.d === o.d; }
  toNumber() { return Number(this.n) / Number(this.d); }
  toString() { return this.d === 1n ? `${this.n}` : `${this.n}/${this.d}`; }
}

export const ZERO_Q = new Fraction(0n);
export const ONE_Q = new Fraction(1n);
