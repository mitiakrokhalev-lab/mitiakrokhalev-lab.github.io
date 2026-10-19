import { CFrac } from './complex-fraction.js';
import { Rational } from './rational.js';

// Кольцо образующих одного построения.
//
// Ключевая мысль: разные виды точек — это НЕ разные случаи в коде, а одно и то
// же, отличающееся только правилом сопряжения. У каждой образующей v хранится
// conj(v) как рациональная функция в этом же кольце:
//
//   на описанной окружности   conj(v) = 1/v
//   свободная на плоскости    conj(v) = v̄  (заводится вторая образующая)
//   на окружности (o, r²)     conj(v) = ō + r²/(v − o)
//   на прямой z + βz̄ = δ      conj(v) = (δ − v)/β
//
// Дальше Rational#conjugate() — просто подстановка этих правил в каждый
// одночлен плюс сопряжение коэффициента. Никакого разбора случаев.
//
// Все четыре правила — инволюции (conj(conj(v)) = v), это проверяется тестом.
export class Ring {
  constructor() {
    this.vars = [];        // { name, tex, kind, conj: Rational|null }
    this.unitIndices = []; // образующие на описанной окружности
  }

  get names() { return this.vars.map(v => v.name); }
  get texNames() { return this.vars.map(v => v.tex); }
  get size() { return this.vars.length; }

  indexOf(name) { return this.vars.findIndex(v => v.name === name); }

  constant(x) {
    const c = x instanceof CFrac ? x : new CFrac(BigInt(x));
    return Rational.fromConstant(this, c);
  }

  // Константы неизменяемы и запрашиваются постоянно — держим по одной штуке.
  zero() { return (this._zero ??= this.constant(0n)); }
  one() { return (this._one ??= this.constant(1n)); }
  i() { return (this._i ??= this.constant(new CFrac(0n, 1n))); }

  variable(name) {
    const idx = this.indexOf(name);
    if (idx < 0) throw new Error(`неизвестная образующая ${name}`);
    return Rational.fromVariable(this, idx);
  }

  conjOf(index) {
    const rule = this.vars[index].conj;
    if (!rule) throw new Error(`у образующей ${this.vars[index].name} нет правила сопряжения`);
    return rule;
  }

  #push(name, tex, kind) {
    this.vars.push({ name, tex, kind, conj: null });
    return this.vars.length - 1;
  }

  // ВЕЩЕСТВЕННАЯ образующая: conj(v) = v. Такие нужны Бариканатору — там
  // буквы это длины сторон a, b, c, а они вещественные, и никакой связи между
  // ними нет. Правило сопряжения всё равно заводится: тогда весь остальной
  // движок (сопряжение, сравнение, печать) работает над ними без единой правки.
  scalar(name, tex = name) {
    const i = this.#push(name, tex, 'real');
    const v = Rational.fromVariable(this, i);
    this.vars[i].conj = v;
    return v;
  }

  // Точка на описанной окружности (она же единичная): conj(v) = 1/v.
  unitPoint(name, tex = name) {
    const i = this.#push(name, tex, 'unit');
    const v = Rational.fromVariable(this, i);
    this.vars[i].conj = this.one().div(v);
    this.unitIndices.push(i);
    return v;
  }

  // Произвольная точка плоскости: заводит ДВЕ образующие, v и v̄, взаимно
  // сопряжённые. Никакого соотношения между ними нет — так и должно быть.
  freePoint(name) {
    const i = this.#push(name, name, 'free');
    const j = this.#push(`${name}̄`, `\\bar{${name}}`, 'conj');
    const v = Rational.fromVariable(this, i);
    const w = Rational.fromVariable(this, j);
    this.vars[i].conj = w;
    this.vars[j].conj = v;
    return v;
  }

  // Точка, бегающая по окружности с центром o и квадратом радиуса r²:
  // (v − o)(v̄ − ō) = r²  ⟹  conj(v) = ō + r²/(v − o).
  pointOnCircle(name, center, r2) {
    const i = this.#push(name, name, 'onCircle');
    const v = Rational.fromVariable(this, i);
    this.vars[i].conj = center.conjugate().add(r2.div(v.sub(center)));
    // Помимо правила сопряжения запоминаем саму окружность.
    //
    // По правилу видно, что точка на ней лежит, но ВЫБРАТЬ по нему конкретную
    // точку нельзя: это уравнение, а не параметризация. Численному слою нужно
    // именно выбрать — поставить случайный треугольник, — и без этих двух полей
    // он такую образующую просто не умел ставить.
    this.vars[i].locus = { kind: 'circle', center, r2 };
    return v;
  }

  // Точка, бегающая по прямой z + β·z̄ = δ:  conj(v) = (δ − v)/β.
  pointOnLine(name, line) {
    const i = this.#push(name, name, 'onLine');
    const v = Rational.fromVariable(this, i);
    this.vars[i].conj = line.rhs().sub(v).div(line.beta);
    this.vars[i].locus = { kind: 'line', line };   // зачем — см. pointOnCircle
    return v;
  }

  // Человекочитаемое описание правила — для панели. У свободной точки писать
  // «d̄ = d̄» бессмысленно, там важно именно то, что связи нет.
  describeConj(name) {
    const i = this.indexOf(name);
    if (i < 0) return '';
    const v = this.vars[i];
    if (v.kind === 'free') return `${v.name}̄ — независима`;
    return `${v.name}̄ = ${v.conj.toString()}`;
  }
}
