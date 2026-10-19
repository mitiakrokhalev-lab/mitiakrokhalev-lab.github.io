import * as P from '../symbolic/poly.js';
import { checkComputeBudget, BudgetExceeded } from '../symbolic/budget.js';

// Превращает символьное выражение в ОПРЕДЕЛЕНИЕ для GeoGebra.
//
// Раньше найденная решателем точка ставилась по вычисленным координатам и
// фиксировалась. Получалась не точка, а картинка: она никуда не двигалась сама,
// не пересчитывалась при сохранении файла, и с ней нельзя было работать
// инструментами. Теперь мы отдаём GeoGebra настоящее выражение через A, B, C —
// и она сама делает точку зависимой со всеми вытекающими.
//
// GeoGebra умеет комплексную арифметику: ToComplex(точка) даёт комплексное
// число, ToPoint(число) — обратно, conjugate() сопрягает, мнимая единица — ί
// (U+03AF, не латинская i: та занята под имена).
export const IMAGINARY_UNIT = 'ί';

function coeffToGgb(coeff) {
  const re = coeff.re;
  const im = coeff.im;
  const part = f => (f.d === 1n ? `${f.n}` : `${f.n}/${f.d}`);
  if (im.isZero()) return part(re);
  const imStr = `${part(im)}*${IMAGINARY_UNIT}`;
  if (re.isZero()) return imStr;
  return `(${part(re)} + ${imStr})`;
}

function polyToGgb(poly, varNames) {
  checkComputeBudget();
  const terms = poly.terms();
  if (terms.length === 0) return '0';
  terms.sort((x, y) => P.compareExp(x.exp, y.exp));
  const parts = [];
  for (const { exp, coeff } of terms) {
    const factors = [];
    const isOne = coeff.re.equals(1n) && coeff.im.isZero();
    const isMinusOne = coeff.re.equals(-1n) && coeff.im.isZero();
    for (let v = 0; v < exp.length; v++) {
      if (!exp[v]) continue;
      const name = varNames[v];
      if (!name) throw new Error(`нет имени GeoGebra для образующей ${v}`);
      factors.push(exp[v] === 1 ? `(${name})` : `(${name})^${exp[v]}`);
    }
    if (factors.length === 0) parts.push(coeffToGgb(coeff));
    else if (isOne) parts.push(factors.join('*'));
    else if (isMinusOne) parts.push(`-${factors.join('*')}`);
    else parts.push(`${coeffToGgb(coeff)}*${factors.join('*')}`);
  }
  return parts.reduce((acc, p) => (acc === '' ? p : (p.startsWith('-') ? `${acc} - ${p.slice(1)}` : `${acc} + ${p}`)), '');
}

// varNames[i] — выражение GeoGebra для i-й образующей (уже в нормированных
// координатах, то есть на единичной окружности).
export function rationalToGgb(rational, varNames) {
  const num = polyToGgb(rational.num, varNames);
  if (P.isOne(rational.den)) return `(${num})`;
  return `((${num}) / (${polyToGgb(rational.den, varNames)}))`;
}

// Значение из квадратичного расширения (quadratic-ext.js) в определение
// GeoGebra. Радикала здесь НЕТ и быть не должно.
//
// Соблазн — написать x = (S + sqrt(S²−4Q))/2 — плох тем, что какую из двух
// ветвей выберет GeoGebra, неизвестно и непроверяемо без живого апплета. Но
// радикал и не нужен: x по построению есть пересечение прямой с окружностью, а
// пересекать GeoGebra умеет сама. Поэтому мост заранее рисует эту пару, берёт
// Intersect(..., 1) и кладёт нормированное выражение этой точки в ext.ggbRoot —
// после чего x становится обычной точкой чертежа.
//
// Вопрос «какой из корней наш» при этом просто исчезает: соотношения x+y = S и
// x·y = Q верны при любом выборе, так что выбор — соглашение, а не факт.
//
// Рекурсия здесь не для красоты: у второго уровня башни коэффициенты сами
// лежат в первом расширении, и разворачиваются этой же функцией.
export function valueToGgb(value, varNames) {
  if (!value?.isAlg) return rationalToGgb(value, varNames);

  const a = valueToGgb(value.a, varNames);
  if (value.b.isZero()) return a;

  const root = value.ext.ggbRoot;
  if (!root) throw new Error('присоединённый корень ещё не построен на чертеже');
  const b = valueToGgb(value.b, varNames);
  if (value.a.isZero()) return `((${b})*(${root}))`;
  return `((${a}) + (${b})*(${root}))`;
}

// Предел на размер определения, отдаваемого GeoGebra.
//
// Выражение разворачивается до самых вершин a, b, c, поэтому объект, построенный
// поверх объекта поверх объекта, переписывает всю цепочку заново: точка на
// касательной — четыре сотни знаков, прямая через неё — уже под шесть тысяч.
// Само по себе это ещё считается, но дальше GeoGebra пересчитывает такую
// простыню на КАЖДОЕ обновление чертежа, и вкладка встаёт — причём внутри самой
// GeoGebra, куда никакой наш бюджет не дотягивается.
//
// Поэтому: считаем и показываем формулу всегда, а на чертёж ставим только то,
// что GeoGebra способна переварить без ущерба для отзывчивости.
const MAX_DEFINITION = 2000;

// Можно ли вообще выразить значение через объекты чертежа: у рационального —
// всегда, у значения с корнем — только когда корень уже нарисован. И в любом
// случае — только если определение выходит обозримым.
export function isDrawableValue(value) {
  if (!hasRoots(value)) return false;
  try {
    return valueToGgb(value, PROBE_NAMES).length <= MAX_DEFINITION;
  } catch (e) {
    // Исчерпанный бюджет ГЛОТАТЬ нельзя: он означает «остановись и скажи», а
    // не «считай, что рисовать нечего». Проглоченный, он превращал честную
    // остановку в молчаливое продолжение — и вкладка вставала дальше.
    if (e instanceof BudgetExceeded) throw e;
    return false;
  }
}

function hasRoots(value) {
  if (!value?.isAlg) return true;
  if (value.b.isZero()) return hasRoots(value.a);
  return !!value.ext.ggbRoot && hasRoots(value.a) && hasRoots(value.b);
}

// Для оценки размера имена образующих не важны — важна длина. Берём короткие
// заглушки: настоящие имена той же природы («cmplA»), так что оценка честная.
const PROBE_NAMES = new Proxy({}, { get: () => 'cmplA' });
