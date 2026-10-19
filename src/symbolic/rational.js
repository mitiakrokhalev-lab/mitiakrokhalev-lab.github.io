import { CFrac, ONE, ZERO } from './complex-fraction.js';
import { Fraction } from './fraction.js';
import * as P from './poly.js';
import { polyGcd, divideExact, factorPoly, polySqrt, checkComputeBudget } from './gcd.js';
import { factorFully } from './multifactor.js';
import { checkIfHeavy } from './budget.js';

// Рациональная функция num/den над образующими одного кольца.
// Кольцо носится с собой: от него зависят и сопряжение (у каждой образующей
// своё правило), и список кандидатов на сокращение.
export class Rational {
  constructor(ring, num, den) {
    if (den.isZero()) throw new Error('Rational: нулевой знаменатель');
    this.ring = ring;
    this.num = num;
    this.den = den;
  }

  static fromConstant(ring, x) {
    const c = x instanceof CFrac ? x : new CFrac(BigInt(x));
    return new Rational(ring, P.constant(c), P.constant(ONE));
  }

  static fromVariable(ring, index) {
    return new Rational(ring, P.variable(index), P.constant(ONE));
  }

  // Поднять число до Rational в ТОМ ЖЕ кольце — чтобы формулы могли писать
  // просто .div(2n), не таская готовых констант.
  lift(x) {
    if (x instanceof Rational) {
      if (x.ring !== this.ring) throw new Error('Rational: выражения из разных колец');
      return x;
    }
    return Rational.fromConstant(this.ring, x);
  }

  #make(num, den) { return new Rational(this.ring, num, den).reduce(); }

  reduce() {
    if (this.num.isZero()) return new Rational(this.ring, P.zero(), P.constant(ONE));

    let num = this.num;
    let den = this.den;
    // Сокращаем на НАСТОЯЩИЙ НОД. Без этого числитель и знаменатель растут на
    // каждом построении, и через несколько шагов движок встаёт — ровно это и
    // происходило со списком кандидатов, который сюда не дотягивался.
    if (!P.isOne(den)) {
      const g = polyGcd(num, den);
      if (!P.isOne(g)) {
        const qn = divideExact(num, g);
        const qd = divideExact(den, g);
        if (qn && qd) { num = qn; den = qd; }
      }
    }

    // Дробь определена с точностью до общего скалярного множителя, а сокращение
    // множителей его не фиксирует. Без нормировки вылезает и (a+b)/(-1), и
    // «1/2b» — последнее вообще читается как 1/(2b). Поэтому:
    // 1) старший коэффициент знаменателя приводим к единице,
    const lead = P.leadingCoeff(den);
    if (lead && !lead.isOne()) {
      const inv = ONE.div(lead);
      num = P.scale(num, inv);
      den = P.scale(den, inv);
    }
    // 2) вычищаем дроби из коэффициентов — они уезжают в знаменатель целиком,
    const lcm = P.bigLcm(P.coeffDenomLcm(num), P.coeffDenomLcm(den));
    if (lcm !== 1n) {
      const f = new CFrac(lcm, 0n);
      num = P.scale(num, f);
      den = P.scale(den, f);
    }
    // 3) снимаем общий целый множитель, чтобы 2a/2 не осталось в таком виде.
    const g = P.bigGcd(P.coeffNumGcd(num), P.coeffNumGcd(den));
    if (g > 1n) {
      const f = new CFrac(new Fraction(1n, g), 0n);
      num = P.scale(num, f);
      den = P.scale(den, f);
    }
    return new Rational(this.ring, num, den);
  }

  // Общий знаменатель берётся как НОК, а не как произведение. Знаменатели тут
  // почти всегда родственники: оба выросли из правил сопряжения одного и того
  // же построения, и сплошь и рядом один нацело делит другой. Наивное
  // произведение раздувает обе части дроби, а следом reduce() гоняет
  // многомерный НОД уже по раздутым многочленам — стоимость растёт куда
  // быстрее линейного. На пересечении двух описанных окружностей (точки на
  // сторонах треугольника) это 1269/687 членов вместо 183/95: минуты против
  // миллисекунд.
  #combine(o, op) {
    // Бюджет проверяется на входе в КАЖДУЮ операцию, а не только в НОДе:
    // между вызовами НОДа лежат умножения многочленов и сопряжения, и одного
    // такого умножения на больших выражениях хватает на секунды.
    checkComputeBudget();
    o = this.lift(o);
    // Равные знаменатели — самый частый случай, и НОД тут не нужен вовсе.
    if (P.equals(this.den, o.den)) return this.#make(op(this.num, o.num), this.den);
    const g = polyGcd(this.den, o.den);
    if (!P.isOne(g)) {
      const co1 = divideExact(o.den, g);          // o.den / g
      const co2 = divideExact(this.den, g);       // this.den / g
      if (co1 && co2) {
        return this.#make(op(P.mul(this.num, co1), P.mul(o.num, co2)),
                          P.mul(this.den, co1));  // = НОК
      }
    }
    return this.#make(op(P.mul(this.num, o.den), P.mul(o.num, this.den)),
                      P.mul(this.den, o.den));
  }

  // Значение из квадратичного расширения (quadratic-ext.js) — не Rational, но
  // базовое поле в него ВЛОЖЕНО, поэтому смешанная операция вполне осмысленна:
  // передаём её расширению, развернув порядок там, где он важен.
  //
  // Без этих четырёх строк расширение было бы бесполезно на практике: стоит
  // одной иррациональной точке появиться на чертеже, как она немедленно
  // встречается с обычными коэффициентами прямых и окружностей — и всё
  // валится на `Rational.lift`. Опознаём по метке, а не по instanceof, чтобы
  // не заводить кольцевой импорт (расширение само импортирует Rational).
  add(o) { return o?.isAlg ? o.add(this) : this.#combine(o, P.add); }
  sub(o) { return o?.isAlg ? o.neg().add(this) : this.#combine(o, P.sub); }
  // Перекрёстное сокращение ДО умножения, а не после.
  //
  // Наивное «перемножить и сократить» отдаёт reduce() уже раздутое
  // произведение, а стоимость многомерного НОДа растёт куда быстрее линейного:
  // сократить два маленьких сомножителя несравнимо дешевле, чем один большой
  // результат. Цена — два НОДа на маленьких входах, и они почти всегда уходят
  // в быстрый путь по одночлену.
  //
  // Мера, ради которой это сделано: норма значения из квадратичного расширения
  // (прямая через точку на касательной) считалась 63 секунды при том, что и
  // вход, и ответ — три десятка членов. Всё время уходило в промежуточные
  // произведения, которые тут же сокращались обратно.
  mul(o) {
    if (o?.isAlg) return o.mul(this);
    checkComputeBudget();
    o = this.lift(o);
    let n1 = this.num, d1 = this.den;
    let n2 = o.num, d2 = o.den;

    if (!P.isOne(d2)) {
      const g = polyGcd(n1, d2);
      if (!P.isOne(g)) {
        const qn = divideExact(n1, g), qd = divideExact(d2, g);
        if (qn && qd) { n1 = qn; d2 = qd; }
      }
    }
    if (!P.isOne(d1)) {
      const g = polyGcd(n2, d1);
      if (!P.isOne(g)) {
        const qn = divideExact(n2, g), qd = divideExact(d1, g);
        if (qn && qd) { n2 = qn; d1 = qd; }
      }
    }
    return this.#make(P.mul(n1, n2), P.mul(d1, d2));
  }
  div(o) {
    if (o?.isAlg) return o.inv().mul(this);
    checkComputeBudget();
    o = this.lift(o);
    if (o.num.isZero()) throw new Error('Rational: деление на ноль');
    return this.#make(P.mul(this.num, o.den), P.mul(this.den, o.num));
  }
  neg() { return new Rational(this.ring, P.neg(this.num), this.den); }
  // Точный квадратный корень, если он есть в поле. После reduce() числитель и
  // знаменатель взаимно просты, поэтому дробь — квадрат ровно тогда, когда
  // квадратами оказались обе части.
  sqrt() {
    const num = polySqrt(this.num);
    if (!num) return null;
    const den = polySqrt(this.den);
    if (!den) return null;
    return new Rational(this.ring, num, den).reduce();
  }

  inv() { return this.ring.one().div(this); }

  isZero() { return this.num.isZero(); }
  equals(o) {
    if (o?.isAlg) return o.equals(this);
    o = this.lift(o);
    if (o === this) return true;
    // Оба выражения приведены, поэтому при совпавших знаменателях достаточно
    // сравнить числители — это линейно, а перекрёстное умножение квадратично.
    if (P.equals(this.den, o.den)) return P.equals(this.num, o.num);
    return P.equals(P.mul(this.num, o.den), P.mul(o.num, this.den));
  }

  // Сопряжение: подставить в каждый одночлен правило conj для каждой
  // образующей и сопрячь коэффициент. Правила задаёт кольцо (см. ring.js),
  // поэтому здесь нет ни одного частного случая.
  conjugate() {
    // Одно и то же выражение сопрягают по нескольку раз: LineEq.throughPoints
    // берёт conj обеих точек дважды, ratioIsReal — обоих сомножителей, и так
    // далее. Выражения неизменяемы, поэтому результат можно просто запомнить.
    if (!this._conj) {
      this._conj = conjPoly(this.ring, this.num).div(conjPoly(this.ring, this.den));
      this._conj._conj = this;                       // сопряжение — инволюция
    }
    return this._conj;
  }

  evalAt(values) {
    return P.evalPoly(this.num, values).div(P.evalPoly(this.den, values));
  }

  // Подставить вместо образующих готовые выражения ДРУГОГО кольца.
  // Так решение системы, найденное в маленьком локальном кольце (где каждая
  // построенная точка — просто буква), раскрывается через a, b, c ровно один
  // раз, в самом конце. Считать всю систему сразу в главном кольце было бы
  // на порядки дороже.
  substituteInto(values) {
    const target = values.find(Boolean)?.ring;
    if (!target) throw new Error('substituteInto: нечего подставлять');

    // Среди подставляемых точек может оказаться иррациональная — тогда весь
    // трюк с общим знаменателем неприменим: у элемента расширения нет ни
    // `num`, ни `den`, он устроен как пара `a + b·x`. Считаем в лоб, обычной
    // арифметикой того поля, где значения живут: она сама разберётся и со
    // смешением этажей, и со встречей рациональной точки с иррациональной.
    // Дороже, зато работает; а срабатывает эта ветвь только когда радикал в
    // построении действительно есть.
    if (values.some(v => v?.isAlg)) {
      const evalIn = poly => {
        checkIfHeavy(poly.size);
        let acc = null;
        for (const { exp, coeff } of poly.terms()) {
          let term = target.constant(coeff);
          for (let v = 0; v < exp.length; v++) {
            if (!exp[v]) continue;
            if (!values[v]) throw new Error(`substituteInto: нет значения для образующей ${v}`);
            for (let p = 0; p < exp[v]; p++) term = term.mul(values[v]);
          }
          acc = acc ? acc.add(term) : term;
        }
        return acc ?? target.zero();
      };
      const denom = evalIn(this.den);
      if (denom.isZero()) throw new Error('substituteInto: знаменатель обратился в ноль');
      return evalIn(this.num).div(denom);
    }

    // Собираем через общий знаменатель, а не перемножая Rational по одному:
    // каждое такое умножение звало бы reduce(), то есть НОД, и подстановка в
    // выражение из двух десятков членов занимала секунды вместо миллисекунд.
    const expand = poly => {
      const ts = poly.terms();
      if (ts.length === 0) return { num: P.zero(), den: P.constant(ONE) };
      const maxExp = [];
      for (const t of ts) {
        for (let v = 0; v < t.exp.length; v++) maxExp[v] = Math.max(maxExp[v] ?? 0, t.exp[v]);
      }
      for (let v = 0; v < maxExp.length; v++) {
        if ((maxExp[v] ?? 0) > 0 && !values[v]) {
          throw new Error(`substituteInto: нет значения для образующей ${v}`);
        }
      }
      let numAcc = P.zero();
      for (const t of ts) {
        let n = P.constant(t.coeff);
        for (let v = 0; v < maxExp.length; v++) {
          const m = maxExp[v] ?? 0;
          if (m === 0) continue;
          const e = t.exp[v] ?? 0;
          n = P.mul(n, P.pow(values[v].num, e));
          n = P.mul(n, P.pow(values[v].den, m - e));     // добиваем до общего знаменателя
        }
        numAcc = P.add(numAcc, n);
      }
      let denAcc = P.constant(ONE);
      for (let v = 0; v < maxExp.length; v++) {
        const m = maxExp[v] ?? 0;
        if (m > 0) denAcc = P.mul(denAcc, P.pow(values[v].den, m));
      }
      return { num: numAcc, den: denAcc };
    };
    const a = expand(this.num);
    const b = expand(this.den);
    if (b.num.isZero()) throw new Error('substituteInto: знаменатель обратился в ноль');
    return new Rational(target, P.mul(a.num, b.den), P.mul(a.den, b.num)).reduce();
  }

  // Приближённое вычисление в обычных комплексных числах — для сверки с
  // чертежом. Возвращает { re, im }; NaN, если знаменатель обнулился.
  evalFloat(values) {
    const n = P.evalPolyFloat(this.num, values);
    const d = P.evalPolyFloat(this.den, values);
    const q = d.re * d.re + d.im * d.im;
    if (q === 0) return { re: NaN, im: NaN };
    return { re: (n.re * d.re + n.im * d.im) / q, im: (n.im * d.re - n.re * d.im) / q };
  }

  // "Простое" = печатается так, что его можно вставить в бо́льшую формулу без
  // скобок. После разложения на множители это уже не «один одночлен»:
  // (a−b)(a+c) тоже вставляется без внешних скобок.
  isSimple() { return P.isOne(this.den) && factoredForm(this.num, this.ring.names, false).atomic; }

  toString() { return this.#render(this.ring.names, false); }
  toTex() { return this.#render(this.ring.texNames, true); }

  // Развёрнутый вид, без разложения на скобки — нужен тестам и отладке.
  toExpandedString() {
    const numStr = polyToString(this.num, this.ring.names);
    if (P.isOne(this.den)) return numStr;
    const denStr = polyToString(this.den, this.ring.names);
    const numOut = this.num.size > 1 ? `(${numStr})` : numStr;
    return `${numOut}/${isBareDenominator(this.den) ? denStr : `(${denStr})`}`;
  }

  #render(names, tex) {
    const num = factoredForm(this.num, names, tex);
    if (P.isOne(this.den)) return num.text;
    const den = factoredForm(this.den, names, tex);
    if (tex) return `\\frac{${num.text}}{${den.text}}`;
    const numOut = num.atomic ? num.text : `(${num.text})`;
    const denOut = den.atomic && isBareDenominator(this.den) ? den.text : `(${den.text})`;
    return `${numOut}/${denOut}`;
  }
}

// Печатает многочлен произведением неприводимых множителей: -2(a−b)(a+b+c)².
// Именно этого не хватало больше всего — развёрнутые формулы на страницу A4
// нечитаемы, а разложенные обычно занимают строку.
//
// atomic = результат можно вставлять в бо́льшую формулу без внешних скобок.
// Не атомарен ровно один случай: многочлен не разложился, и наружу выходит
// голая сумма вроде «a + b».
function factoredForm(poly, names, tex, given = null) {
  // Печать — тоже работа, и на огромном многочлене она идёт долго. Без этой
  // проверки счёт укладывался в бюджет, а вкладка всё равно вставала: уже на
  // разложении и выводе.
  checkComputeBudget();
  const { content, factors } = given ?? factorPoly(poly);
  if (factors.length === 0) {
    const text = polyToString(poly, names);
    return { text, atomic: poly.size <= 1 };
  }

  const parts = [];
  let sign = '';
  if (!content.isOne()) {
    if (content.im.isZero() && content.re.equals(-1n)) sign = '-';
    else parts.push(content.toString());
  }
  for (const { poly: f, power } of factors) {
    const body = polyToString(f, names);
    const bare = f.size <= 1;
    const wrapped = bare ? body : `(${body})`;
    parts.push(power === 1 ? wrapped : `${wrapped}${tex ? `^{${power}}` : `^${power}`}`);
  }
  if (parts.length === 0) return { text: sign === '-' ? '-1' : '1', atomic: true };

  // Единственный множитель без степени и без числового коэффициента печатаем
  // без внешних скобок — их поставит тот, кому они нужны.
  if (parts.length === 1 && sign === '' && factors[0].power === 1 && factors[0].poly.size > 1) {
    return { text: polyToString(factors[0].poly, names), atomic: false };
  }

  // Пробел нужен только между «голыми» множителями: «b c» и «a^2 b», но
  // «2a», «2(a+b)» и «(a-b)(a+c)» слитно.
  const isNumber = t => /^-?\d+(?:\/\d+)?$/.test(t);
  let out = sign;
  let prev = null;
  for (const part of parts) {
    if (prev !== null && !part.startsWith('(') && !isNumber(prev)) out += ' ';
    out += part;
    prev = part;
  }
  return { text: out, atomic: true };
}

// conj(P) как рациональная функция. Собирается через общий знаменатель, чтобы
// не звать reduce() на каждом слагаемом: конъюгат каждой образующей — дробь
// N_i/D_i, одночлен ∏x_i^{e_i} переходит в (∏N_i^{e_i})/(∏D_i^{e_i}), и общий
// знаменатель для всей суммы — ∏D_i^{max e_i}.
function conjPoly(ring, poly) {
  checkComputeBudget();
  const ts = poly.terms();
  if (ts.length === 0) return ring.zero();

  const maxExp = [];
  for (const t of ts) {
    for (let v = 0; v < t.exp.length; v++) {
      maxExp[v] = Math.max(maxExp[v] ?? 0, t.exp[v]);
    }
  }

  const rule = [];
  for (let v = 0; v < maxExp.length; v++) {
    if ((maxExp[v] ?? 0) > 0) rule[v] = ring.conjOf(v);
  }

  // Правило сопряжения образующей может само лежать в квадратичном расширении:
  // ровно так выходит у точки, посаженной на КАСАТЕЛЬНУЮ из внешней точки —
  // коэффициенты той прямой содержат присоединённый корень. Быстрый путь ниже
  // собирает всё на уровне многочленов через num/den, а у такого правила ни
  // числителя, ни знаменателя нет, и он падал с невнятным «Cannot read
  // properties of undefined». Поэтому отдельный общий путь: считаем прямо в
  // поле обычными операциями. Он дороже, но включается только когда без него
  // не обойтись, так что на обычные построения не влияет.
  const extended = rule.find(r => r?.isAlg);
  if (extended) {
    const target = extended.ring;
    let acc = target.zero();
    for (const t of ts) {
      let term = target.constant(t.coeff.conj());
      for (let v = 0; v < maxExp.length; v++) {
        const e = t.exp[v] ?? 0;
        for (let k = 0; k < e; k++) term = term.mul(rule[v]);
      }
      acc = acc.add(term);
    }
    return acc;
  }

  let numAcc = P.zero();
  for (const t of ts) {
    let n = P.constant(t.coeff.conj());
    for (let v = 0; v < maxExp.length; v++) {
      const e = t.exp[v] ?? 0;
      const m = maxExp[v] ?? 0;
      if (m === 0) continue;
      n = P.mul(n, P.pow(rule[v].num, e));          // N_v^{e}
      n = P.mul(n, P.pow(rule[v].den, m - e));      // добиваем до общего знаменателя
    }
    numAcc = P.add(numAcc, n);
  }

  let denAcc = P.constant(ONE);
  for (let v = 0; v < maxExp.length; v++) {
    const m = maxExp[v] ?? 0;
    if (m > 0) denAcc = P.mul(denAcc, P.pow(rule[v].den, m));
  }
  return new Rational(ring, numAcc, denAcc).reduce();
}

function coeffToString(coeff, needSign) {
  if (!coeff.im.isZero()) return (needSign ? ' + ' : '') + `(${coeff.toString()})`;
  const val = coeff.re;
  const negative = val.n < 0n;
  const abs = negative ? val.neg() : val;
  const sign = needSign ? (negative ? ' - ' : ' + ') : (negative ? '-' : '');
  return sign + (abs.equals(1n) ? '' : abs.toString());
}

function monomialString(exp, names) {
  const parts = [];
  for (let v = 0; v < exp.length; v++) {
    if (exp[v] === 1) parts.push(names[v]);
    else if (exp[v] > 1) parts.push(`${names[v]}^${exp[v]}`);
  }
  return parts.join(' ');
}

function polyToString(poly, names) {
  checkComputeBudget();
  const ts = poly.terms();
  if (ts.length === 0) return '0';
  ts.sort((x, y) => P.compareExp(x.exp, y.exp));
  let out = '';
  ts.forEach((t, idx) => {
    const mono = monomialString(t.exp, names);
    const coeffStr = coeffToString(t.coeff, idx > 0);
    if (mono === '') {
      out += (coeffStr === '' || coeffStr === ' + ' || coeffStr === ' - ' || coeffStr === '-')
        ? coeffStr + '1' : coeffStr;
    } else {
      out += coeffStr + mono;
    }
  });
  return out.trim();
}

// Без скобок знаменатель можно оставить только если он читается однозначно:
// голое число (/2) или одна буква (/a). Уже «/2a» и «/a b» читаются как
// (x/2)·a и (x/a)·b.
function isBareDenominator(poly) {
  const ts = poly.terms();
  if (ts.length !== 1) return false;
  const { exp, coeff } = ts[0];
  const deg = exp.reduce((s, e) => s + e, 0);
  if (deg === 0) return true;
  return deg === 1 && coeff.isOne();
}

// ---- полное разложение по требованию ---------------------------------------

// Та же печать, но множители берутся у ПОЛНОГО разложения (multifactor.js), а
// не у дешёвого. Зовётся только по явной просьбе пользователя: полное
// разложение вправе думать секунды, а печать в панели — нет.
//
// Если разложить до конца не вышло, честно возвращаем null: пусть строка
// останется прежней, чем притворится, будто это и есть неприводимый вид.
export function fullyFactored(rational, tex, rnd) {
  const names = tex ? rational.ring.texNames : rational.ring.names;
  const num = factorFully(rational.num, rnd);
  if (!num) return null;
  const numText = factoredForm(rational.num, names, tex, num);
  if (P.isOne(rational.den)) return numText.text;

  const den = factorFully(rational.den, rnd);
  if (!den) return null;
  const denText = factoredForm(rational.den, names, tex, den);
  if (tex) return `\frac{${numText.text}}{${denText.text}}`;
  const numOut = numText.atomic ? numText.text : `(${numText.text})`;
  const denOut = denText.atomic ? denText.text : `(${denText.text})`;
  return `${numOut}/${denOut}`;
}
