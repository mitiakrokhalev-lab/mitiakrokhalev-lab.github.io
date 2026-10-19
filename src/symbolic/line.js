import * as P from './poly.js';
import { polyGcd, divideExact } from './gcd.js';
import { Rational } from './rational.js';
import { CFrac, ONE } from './complex-fraction.js';
import { Fraction } from './fraction.js';

// Symbolic equation of a line.
//
// Через две точки p, q общее уравнение прямой в комплексных числах:
//     z(p̄ - q̄) - z̄(p - q) + (p q̄ - p̄ q) = 0,
// то есть A·z + B·z̄ + C = 0 с
//     A = p̄ - q̄,   B = q - p,   C = p q̄ - p̄ q.
//
// Общий вид не канонический: любое ненулевое кратное задаёт ту же прямую, так
// что «одна и та же» прямая, построенная по разным парам точек, давала бы
// разные коэффициенты. Поэтому храним НОРМИРОВАННЫЙ вид
//
//     z + β·z̄ + γ = 0,      β = B/A,  γ = C/A
//
// (делить на A всегда законно: A = 0 ⟺ p̄ = q̄ ⟺ p = q, то есть прямая
// вырождена). Плюсы:
//   * представление каноническое — зависит только от самой прямой;
//   * для хорды единичной окружности сразу получается классика:
//     β = pq, γ = -(p+q), т.е.  z + pq·z̄ = p + q;
//   * всегда |β| = 1 (β·conj(β) = 1) — дешёвый инвариант для тестов;
//   * z̄ = -(z + γ)/β — ровно то, что нужно подставить в уравнение
//     окружности на следующем шаге (пересечение прямой с окружностью).
export class LineEq {
  constructor(beta, gamma) {
    this.beta = beta;
    this.gamma = gamma;
  }

  static throughPoints(p, q) {
    const A = p.conjugate().sub(q.conjugate());
    if (A.isZero()) throw new Error('LineEq: вырожденная прямая (точки совпали)');
    const B = q.sub(p);
    const C = p.mul(q.conjugate()).sub(p.conjugate().mul(q));
    return new LineEq(B.div(A), C.div(A));
  }

  // Из формы «z + β·z̄ = δ», в которой прямая приходит от касательных,
  // поляр и радикальных осей.
  static fromBetaDelta(beta, delta) { return new LineEq(beta, delta.neg()); }

  get ring() { return this.beta.ring; }

  // Прямая через точку p с заданным β. Направление прямой d связано с β как
  // β = −d/d̄, так что β — это в точности «наклон», и все операции ниже
  // выражаются через него, не требуя пары порождающих точек. Это важно:
  // у касательной, поляры и радикальной оси такой пары нет.
  static throughPointWithBeta(p, beta) {
    return LineEq.fromBetaDelta(beta, p.add(beta.mul(p.conjugate())));
  }

  // Перпендикулярное направление — это i·d, и β при этом меняет знак.
  perpendicularThrough(p) { return LineEq.throughPointWithBeta(p, this.beta.neg()); }

  parallelThrough(p) { return LineEq.throughPointWithBeta(p, this.beta); }

  // Пересечение двух прямых прямо из уравнений: вычитание убирает z,
  // z = (β₂γ₁ − β₁γ₂)/(β₁ − β₂).
  static intersect(l1, l2) {
    const d = l1.beta.sub(l2.beta);
    if (d.isZero()) throw new Error('прямые параллельны или совпадают');
    return l2.beta.mul(l1.gamma).sub(l1.beta.mul(l2.gamma)).div(d);
  }

  // Отражение относительно прямой: z* = δ − β·z̄. Инволютивность держится на
  // |β| = 1 и δ̄ = δ/β — на тех самых инвариантах нормированного вида.
  reflect(z) { return this.rhs().sub(this.beta.mul(z.conjugate())); }

  // Проекция — середина отрезка между точкой и её отражением.
  project(z) { return z.add(this.reflect(z)).div(2n); }

  // z + β·z̄ + γ; ноль ровно тогда, когда z лежит на прямой.
  residual(z) {
    return z.add(this.beta.mul(z.conjugate())).add(this.gamma);
  }

  contains(z) { return this.residual(z).isZero(); }

  // Правая часть в форме «z + β·z̄ = δ».
  rhs() { return this.gamma.neg(); }

  equals(other) {
    return this.beta.equals(other.beta) && this.gamma.equals(other.gamma);
  }

  // Канонический вид A·z + B·z̄ + C = 0 с МНОГОЧЛЕННЫМИ коэффициентами.
  //
  // Нормированная запись (z + βz̄ + γ = 0) хороша тем, что единственна, и
  // именно поэтому по ней сравниваются прямые. Но на бумаге привычнее общий
  // вид без знаменателей, поэтому по кнопке в панели мы домножаем на общий
  // знаменатель и снимаем общий множитель.
  toCanonical() {
    const [A, B, C] = clearDenominators([this.ring.one(), this.beta, this.gamma]);
    return {
      text: canonicalSum('', [[A, 'z'], [B, 'z̄'], [C, '']], r => r.toString(), '(', ')'),
      tex: canonicalSum('', [[A, 'z'], [B, TEX_ZBAR], [C, '']], r => r.toTex(), TEX_OPEN, TEX_CLOSE),
    };
  }

  toString() { return render(this, r => r.toString(), 'z̄', '(', ')'); }

  toTex() { return render(this, r => r.toTex(), '\\bar{z}', '\\left(', '\\right)'); }
}

// Печатает «β·z̄» со знаком, вынесенным наружу, и скобками только там, где они
// действительно нужны (у составных коэффициентов и дробей).
function render(line, str, zbar, open, close) {
  let coeff = str(line.beta);
  let sign = '+';
  const simple = line.beta.isSimple();
  if (simple && coeff.startsWith('-')) { sign = '-'; coeff = coeff.slice(1); }
  const body = simple ? coeff : `${open}${coeff}${close}`;
  const term = body === '1' ? zbar : `${body} ${zbar}`;
  return `z ${sign} ${term} = ${str(line.rhs())}`;
}

const TEX_ZBAR = '\\bar{z}';
const TEX_OPEN = '\\left(';
const TEX_CLOSE = '\\right)';

// Домножает набор дробей на общий знаменатель и снимает общий множитель — и
// многочленный, и числовой. Возвращает Rational с единичным знаменателем,
// чтобы печатать их обычным разложением на множители.
export function clearDenominators(values) {
  const ring = values[0].ring;
  // Общий знаменатель берётся НАИМЕНЬШИМ ОБЩИМ КРАТНЫМ, а не произведением
  // всех подряд. Разница видна там, где дробей много и знаменатели у них
  // одинаковые: у тройки с присоединённым корнем их шесть, и произведение
  // раздувало числители в пятую степень — сокращать потом приходилось уже
  // распухшие многочлены. Для изодинамических точек это была разница между
  // полутора секундами и парой сотен миллисекунд.
  let common = P.constant(ONE);
  for (const v of values) {
    if (P.isOne(v.den)) continue;
    const rest = divideExact(v.den, polyGcd(common, v.den));
    common = P.mul(common, rest ?? v.den);
  }
  let nums = values.map(v => {
    if (v.num.isZero()) return v.num;
    const factor = P.isOne(v.den) ? common : divideExact(common, v.den);
    // Деление обязано пройти по построению кратного; запасной путь оставлен на
    // случай, если многочленное НОД когда-нибудь сдастся по бюджету.
    return P.mul(v.num, factor ?? common);
  });

  let shared = null;
  for (const n of nums) {
    if (n.isZero()) continue;
    shared = shared === null ? n : polyGcd(shared, n);
  }
  if (shared && !P.isOne(shared)) {
    const divided = nums.map(n => (n.isZero() ? n : divideExact(n, shared)));
    if (divided.every(Boolean)) nums = divided;
  }

  let lcm = 1n;
  for (const n of nums) lcm = P.bigLcm(lcm, P.coeffDenomLcm(n));
  if (lcm !== 1n) nums = nums.map(n => P.scale(n, new CFrac(lcm)));
  let g = 0n;
  for (const n of nums) g = P.bigGcd(g, P.coeffNumGcd(n));
  if (g > 1n) nums = nums.map(n => P.scale(n, new CFrac(new Fraction(1n, g))));

  return nums.map(n => new Rational(ring, n, P.constant(ONE)));
}

// Печатает сумму «коэффициент × символ» со знаками наружу и скобками только
// там, где они нужны. lead — уже готовое первое слагаемое: у окружности это
// z z̄, коэффициент при котором всегда единица.
export function canonicalSum(lead, parts, str, open, close) {
  let out = lead;
  for (const [value, symbol] of parts) {
    if (value.isZero()) continue;
    let coeff = str(value);
    const simple = value.isSimple();
    let sign = out === '' ? '' : ' + ';
    // Минус выносим наружу и у дробей — но только когда он относится ко всему
    // выражению: у неразложившейся суммы «-a b + c» отрезать его нельзя.
    if ((simple || coeff.startsWith('-(')) && coeff.startsWith('-')) {
      sign = out === '' ? '-' : ' - ';
      coeff = coeff.slice(1);
    }
    let body;
    if (symbol === '') body = coeff;
    else if (coeff === '1') body = symbol;
    else body = `${simple ? coeff : `${open}${coeff}${close}`} ${symbol}`;
    out += sign + body;
  }
  return `${out === '' ? '0' : out} = 0`;
}

export { TEX_ZBAR, TEX_OPEN, TEX_CLOSE };
