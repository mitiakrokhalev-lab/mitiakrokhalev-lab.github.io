import { CFrac, ONE, ZERO } from './complex-fraction.js';
import { Fraction } from './fraction.js';
import * as P from './poly.js';
import { modularGcd } from './modgcd.js';
import { CeilingExceeded } from './modpoly.js';
import { BudgetExceeded, withComputeBudget, noteSize, lastPeak, checkComputeBudget,
  withSlice, SliceExceeded } from './budget.js';

// Настоящий многомерный НОД и разложение на множители.
//
// Раньше сокращение шло по фиксированному списку кандидатов ((a−b), (a+b+c) и
// т.д.). Это работало на простых формулах и разваливалось на составных: если
// общий множитель в список не попал, дробь не сокращалась, выражения росли на
// каждом построении, и через два-три шага движок вставал. Список кандидатов
// убран целиком — здесь полноценный алгоритм.
//
// Схема классическая: рекурсия по переменным, на каждом уровне многочлен
// раскладывается на содержимое (НОД коэффициентов, считается рекурсивно) и
// примитивную часть, а НОД примитивных частей ищется последовательностью
// псевдоостатков с чисткой содержимого на каждом шаге.

// Гауссовы целые, содержимое, примитивная часть и точное деление переехали в
// polyint.js: тем же самым пользуется модулярный НОД, а импортировать друг
// друга по кругу этим двум нельзя. Здесь они только переэкспортируются, чтобы
// у всех, кто уже берёт их отсюда, ничего не менялось.
import { contentAndPrimitive, primitivePart, divideExact, divides, mainVar,
  gaussGcd, canonicalUnit, gz, gzMul, gzIsZero, gzDivRound, bigAbs } from './polyint.js';
export { contentAndPrimitive, primitivePart, divideExact, divides, CeilingExceeded };

// ---- НОД ------------------------------------------------------------------

function contentInVar(poly, v) {
  let g = P.zero();
  for (const c of P.coeffsIn(poly, v)) {
    if (c.isZero()) continue;
    g = polyGcd(g, c);
    if (P.isOne(g)) break;
  }
  return g.isZero() ? P.constant(ONE) : g;
}

function pseudoRemainder(A, B, v) {
  const db = P.degreeIn(B, v);
  const da = P.degreeIn(A, v);
  const lb = P.coeffsIn(B, v)[db];
  const xv = P.variable(v);
  let R = A;
  let steps = 0;
  while (!R.isZero() && P.degreeIn(R, v) >= db) {
    const dr = P.degreeIn(R, v);
    const lr = P.coeffsIn(R, v)[dr];
    R = P.sub(P.mul(lb, R), P.mul(P.mul(lr, P.pow(xv, dr - db)), B));
    steps++;
  }
  // Псевдоостаток обязан быть СТАНДАРТНЫМ: lc(B)^(deg A − deg B + 1)·A = Q·B + R.
  // Цикл выше домножает на lc(B) по разу за шаг, а шагов бывает меньше — когда
  // степень падает сразу на несколько. Субрезультантная схема на этом ломается
  // молча: её делитель перестаёт делить нацело, «НОД» выходит неверным, и
  // дальше рушится уже деление на содержимое. Добираем недостающие степени.
  for (let i = da - db + 1 - steps; i > 0; i--) R = P.mul(lb, R);
  return R;
}

// ---- эвристический НОД ----------------------------------------------------
//
// Идея: подставить вместо переменной большое число ξ, посчитать НОД получившихся
// (уже более простых) объектов, а потом развернуть его обратно, читая цифры по
// основанию ξ. Если ξ больше удвоенного максимума коэффициентов, цифры не
// переполняются и разворот однозначен.
//
// Ответ обязательно проверяется делением, поэтому неверный результат сюда
// физически не проходит: он просто отвергается, и работает обычный алгоритм.

const HEURISTIC_ATTEMPTS = 4;
// Ограничение не на само ξ, а на РАЗМЕР ПОДСТАВЛЕННЫХ чисел: в многочлен
// степени d подставленное ξ входит как ξ^d, и на каждом уровне рекурсии длина
// умножается на степень. С прежним пределом в 4000 знаков на самом ξ это
// доходило до полусотни тысяч знаков, а Евклид по таким числам считался
// десятками секунд — ровно столько и занимало одно сокращение дроби.
const MAX_DIGITS = 800;

function maxNorm(poly) {
  let m = 1n;
  for (const { coeff } of poly.terms()) {
    m = m > bigAbs(coeff.re.n) ? m : bigAbs(coeff.re.n);
    m = m > bigAbs(coeff.im.n) ? m : bigAbs(coeff.im.n);
  }
  return m;
}

function substitute(poly, v, xi) {
  const out = [];
  for (const { exp, coeff } of poly.terms()) {
    const e = exp[v] ?? 0;
    const next = exp.slice();
    if (v < next.length) next[v] = 0;
    let mult = 1n;
    for (let k = 0; k < e; k++) mult *= xi;
    out.push({ exp: next, coeff: coeff.mul(new CFrac(mult)) });
  }
  return P.fromTerms(out);
}

// Симметричный остаток: цифра лежит в (-ξ/2, ξ/2], иначе разворот неоднозначен.
function symmetricMod(n, xi) {
  let r = n % xi;
  if (2n * r > xi) r -= xi;
  else if (2n * r <= -xi) r += xi;
  return r;
}

function expandDigits(coeff, xi) {
  let re = coeff.re.n, im = coeff.im.n;
  const digits = [];
  while (re !== 0n || im !== 0n) {
    const dr = symmetricMod(re, xi);
    const di = symmetricMod(im, xi);
    digits.push(new CFrac(dr, di));
    re = (re - dr) / xi;
    im = (im - di) / xi;
    if (digits.length > 64) return null;         // не сходится — плохой ξ
  }
  return digits;
}

function reconstruct(poly, v, xi) {
  const out = [];
  for (const { exp, coeff } of poly.terms()) {
    const digits = expandDigits(coeff, xi);
    if (!digits) return null;
    digits.forEach((d, k) => {
      if (d.isZero()) return;
      const next = exp.slice();
      while (next.length <= v) next.push(0);
      next[v] = k;
      out.push({ exp: next, coeff: d });
    });
  }
  return P.fromTerms(out);
}

// База рекурсии ОБЯЗАНА быть целочисленным НОД, а не единицей. В поле числа
// обратимы, и polyGcd честно возвращает 1 — но здесь числа несут в себе степени
// подставленной переменной, и, потеряв их, разворот даёт лишь ДЕЛИТЕЛЬ НОДа.
// Проверка делением такой ответ пропускает, и дробь недосокращается: ровно так
// вылезало «c(b+c)/c» вместо «b+c».
function heuGcdOverIntegers(A, B, depth) {
  if (depth > 4) return null;
  const v = Math.max(mainVar(A), mainVar(B));
  if (v < 0) {
    const toGz = poly => {
      if (poly.isZero()) return gz(0n, 0n);
      const c = poly.terms()[0].coeff;
      if (c.re.d !== 1n || c.im.d !== 1n) return null;   // не целое — не наш случай
      return gz(c.re.n, c.im.n);
    };
    const ga = toGz(A), gb = toGz(B);
    if (!ga || !gb) return null;
    const g = canonicalUnit(gaussGcd(ga, gb));
    return gzIsZero(g) ? null : P.constant(new CFrac(g.re, g.im));
  }

  const degree = Math.max(1, P.degreeIn(A, v), P.degreeIn(B, v));
  let xi = 2n * (maxNorm(A) < maxNorm(B) ? maxNorm(A) : maxNorm(B)) + 2n;
  for (let attempt = 0; attempt < HEURISTIC_ATTEMPTS; attempt++) {
    checkComputeBudget();
    if (xi.toString().length * degree > MAX_DIGITS) return null;
    const a = substitute(A, v, xi);
    const b = substitute(B, v, xi);
    if (!a.isZero() && !b.isZero()) {
      const g = heuGcdOverIntegers(a, b, depth + 1);
      if (g && !g.isZero()) {
        const lifted = reconstruct(g, v, xi);
        if (lifted && !lifted.isZero()
            && divideExact(A, lifted) && divideExact(B, lifted)) return lifted;
      }
    }
    xi = (xi * 73794n) / 27011n;                  // ≈ ×2.73, как в оригинале
  }
  return null;
}

function heuristicGcd(A, B) {
  const a = primitivePart(A), b = primitivePart(B);   // целые гауссовы коэффициенты
  const g = heuGcdOverIntegers(a, b, 0);
  if (!g) return null;
  const cand = primitivePart(g);
  if (P.isOne(cand)) return null;
  return divideExact(A, cand) && divideExact(B, cand) ? cand : null;
}

// Наименьшая степень каждой переменной по всем членам — одночленная часть.
function minDegrees(poly) {
  let mins = null;
  for (const { exp } of poly.terms()) {
    if (mins === null) { mins = exp.slice(); continue; }
    for (let v = 0; v < mins.length; v++) mins[v] = Math.min(mins[v], exp[v] ?? 0);
    mins.length = Math.min(mins.length, exp.length);
  }
  return mins ?? [];
}

function monomialFrom(degs) {
  let m = P.constant(ONE);
  for (let v = 0; v < degs.length; v++) {
    if (degs[v] > 0) m = P.mul(m, P.pow(P.variable(v), degs[v]));
  }
  return m;
}

// Пределы для последовательности псевдоостатков — см. коммент про взаимную
// простоту. 10^400 подобрано так, чтобы обычные выкладки в них укладывались с
// огромным запасом, а разбегание останавливалось за доли секунды.
const PRS_MAX_STEPS = 24;
const PRS_MAX_COEFF = 10n ** 400n;

export function polyGcd(A, B) {
  // Точка проверки бюджета: время уходит именно сюда, а вызовов много, так
  // что одного сравнения на вызов достаточно и стоит оно ничего.
  checkComputeBudget();
  noteSize(A.size > B.size ? A.size : B.size);
  if (A.isZero()) return B.isZero() ? P.constant(ONE) : primitivePart(B);
  if (B.isZero()) return primitivePart(A);

  // Быстрый путь: одночлен. Знаменатели здесь почти всегда одночлены — их
  // порождает сопряжение (conj(a) = 1/a), — и гонять по ним полноценную
  // последовательность псевдоостатков бессмысленно дорого: именно это делало
  // каждое следующее построение вдвое медленнее предыдущего.
  if (A.size === 1 || B.size === 1) {
    const da = minDegrees(A), db = minDegrees(B);
    const n = Math.min(da.length, db.length);
    const out = [];
    for (let v = 0; v < n; v++) out.push(Math.min(da[v], db[v]));
    return monomialFrom(out);
  }

  // Одночленную часть снимаем отдельно и сразу: она находится одним проходом,
  // а вот дорогим алгоритмам мешает — они видят общий множитель, честно его
  // ищут и попутно раздувают всё остальное. Оставшиеся части уже свободны от
  // общих одночленов, и очень часто взаимно просты.
  const monoA = minDegrees(A), monoB = minDegrees(B);
  if (monoA.some(Boolean) || monoB.some(Boolean)) {
    const shift = divideExact(A, monomialFrom(monoA));
    const other = divideExact(B, monomialFrom(monoB));
    const common = [];
    for (let v = 0; v < Math.min(monoA.length, monoB.length); v++) {
      common.push(Math.min(monoA[v], monoB[v]));
    }
    return P.mul(monomialFrom(common), polyGcd(shift, other));
  }

  const top = Math.max(mainVar(A), mainVar(B));
  if (top < 0) return P.constant(ONE);        // обе — константы, поле

  // Дешёвый отсев: НОД не может содержать переменную, которой нет в одном из
  // многочленов. Если таких переменных не осталось совсем — НОД константа.
  const shared = [];
  for (let i = 0; i <= top; i++) {
    if (P.degreeIn(A, i) > 0 && P.degreeIn(B, i) > 0) shared.push(i);
  }
  if (shared.length === 0) return P.constant(ONE);

  // ГЛАВНЫЙ путь — модулярный НОД (modgcd.js).
  //
  // Всё, что написано ниже про перебор главной переменной и растущие сроки,
  // лечило СИМПТОМ: последовательность псевдоостатков раздувает коэффициенты, и
  // цена начинает зависеть от порядка букв. В конечном поле коэффициенты не
  // растут вовсе, поэтому зависимость исчезает как класс, а не смягчается.
  //
  // Модулярный путь отвечает либо верно (ответ проверен делением), либо
  // «не вышло» — и тогда работает всё прежнее, слово в слово как раньше.
  //
  // «Не вышло» осталось ровно одно: показатели не влезли в упаковку одночлена
  // (52 бита). Это требует, чтобы в ОДНОМ выражении сошёлся почти весь алфавит
  // и при этом степени были выше третьей — замер на реальных построениях даёт
  // 18 бит на шести переменных и 30 на десяти, то есть запас двукратный. На
  // контрольном прогоне из девяноста девяти вызовов НОДа сюда не ушёл ни один.
  //
  // Прежняя, куда более частая причина — «кончились простые» — убрана: их
  // теперь выдаёт генератор, а не список из двенадцати (см. fp2.js).
  const modular = modularGcd(primitivePart(A), primitivePart(B));
  if (modular) return modular;

  // Эвристика Char–Fortune–Watt: подставить большое число, взять НОД целых,
  // развернуть обратно по основанию. Работает почти всегда и на порядки
  // быстрее последовательности псевдоостатков, а главное — САМА СЕБЯ ПРОВЕРЯЕТ
  // делением, так что ошибиться не может: не подошло — просто идём дальше.
  // Главную переменную ПЕРЕБИРАЕМ, а не выбираем раз и навсегда.
  //
  // Стоимость последовательности псевдоостатков зависит от этого выбора дико —
  // и это не теория. Окружность через вершину и два основания чевиан считалась
  // 2.5 секунды, а та же самая задача, у которой всего лишь переставили буквы
  // A и B, не считалась за две минуты. Проверено прямо: та же геометрия при
  // порядке букв «b,a,c» — 2.5 с, при «a,b,c» — не уложилась в минуту.
  //
  // Предсказать хорошую переменную заранее нельзя (степени у всех кандидатов
  // одинаковые), зато можно дать каждой короткий срок и, если не уложилась,
  // взять следующую. Сроки растут вчетверо, поэтому суммарные накладные
  // ограничены, а найденный быстрый вариант находится быстро.
  //
  // Порядок кандидатов остаётся осмысленным: сначала переменные с наименьшей
  // степенью — чем меньше шагов деления, тем меньше распухают коэффициенты.
  const candidates = [...shared].sort((i, j) =>
    Math.min(P.degreeIn(A, i), P.degreeIn(B, i)) - Math.min(P.degreeIn(A, j), P.degreeIn(B, j)));

  // Перебор только на ВЕРХНЕМ уровне. Внутри рекурсии он бессмыслен и вреден:
  // вложенные вызовы наследуют срок, тратят его на свои переборы, и хорошие
  // случаи дорожают в разы — проверено, 2.5 секунды превращались в 17.
  // Срок ЩЕДРЫЙ, и это принципиально. Череда коротких сроков выглядит разумнее,
  // но обходится дорого: подавляющее большинство НОДов считается за миллисекунды
  // и от перебора ничего не выигрывает, зато любой, кому нужно чуть больше
  // срока, платит за все неудавшиеся попытки. С шестидесятимиллисекундными
  // сроками прогон тестов раздулся с полуминуты до десяти.
  //
  // Поэтому платит только тот, кто ДЕЙСТВИТЕЛЬНО застрял: обычная работа
  // укладывается в первый срок и о переборе не знает.
  if (candidates.length > 1 && gcdDepth === 0) {
    // Сначала — щедрая попытка по лучшей на вид переменной. Подавляющее
    // большинство работы укладывается сюда и о переборе не знает: это важно,
    // потому что коротких сроков с самого начала прогон тестов не пережил —
    // раздулся с полуминуты до десяти. Платить за перебор должен только тот,
    // кто действительно застрял.
    try {
      return withSlice(PRS_PATIENT_MS, () => gcdAlongVar(A, B, candidates[0]));
    } catch (e) {
      if (!(e instanceof SliceExceeded)) throw e;
    }
    // Не вышло — значит переменная неудачная. Теперь перебираем всех с
    // короткими и растущими сроками: удачная находится быстро.
    for (let slice = PRS_FIRST_SLICE_MS; slice <= PRS_LAST_SLICE_MS; slice *= 4) {
      for (const candidate of candidates.slice(1)) {
        try {
          return withSlice(slice, () => gcdAlongVar(A, B, candidate));
        } catch (e) {
          if (!(e instanceof SliceExceeded)) throw e;
        }
      }
    }
  }
  // Единственный кандидат или все сроки вышли — считаем без ограничения, под
  // общим бюджетом: он и остановит, если задача действительно неподъёмна.
  return gcdAlongVar(A, B, candidates[0]);
}

const PRS_PATIENT_MS = 3000;
const PRS_FIRST_SLICE_MS = 60;
const PRS_LAST_SLICE_MS = 4000;

// НОД по конкретной главной переменной.
let gcdDepth = 0;

function gcdAlongVar(A, B, v) {
  gcdDepth++;
  try { return gcdAlongVarInner(A, B, v); } finally { gcdDepth--; }
}

function gcdAlongVarInner(A, B, v) {
  const ca = contentInVar(A, v);
  const cb = contentInVar(B, v);
  const commonContent = polyGcd(ca, cb);

  let p = divideExact(A, ca);
  let q = divideExact(B, cb);
  if (P.degreeIn(p, v) < P.degreeIn(q, v)) [p, q] = [q, p];

  // Примитивные части взаимно просты ⟹ весь НОД сидит в содержимом. Именно так
  // и бывает чаще всего, а без этой проверки сюда каждый раз заходила
  // последовательность псевдоостатков (см. выше).
  if (coprimeInVar(p, q, v)) return primitivePart(commonContent);

  // Эвристика Char–Fortune–Watt стоит ПОСЛЕ дешёвой проверки, а не до неё.
  //
  // Раньше было наоборот, и это оказалось самой дорогой мелочью движка. НОД в
  // подавляющем большинстве вызовов тривиален, а распознать единицу эвристика
  // не может В ПРИНЦИПЕ: она обязана проверять ответ делением, а единица делит
  // всё, и такой ответ отвергается как бесполезный. То есть в самом частом
  // случае она честно подставляла большие числа, гоняла по ним Евклида и
  // возвращала null. Профиль на окружности через три точки сторон показал 28%
  // всего времени в одной только подстановке — при НУЛЕ успешных попаданий.
  //
  // Теперь она получает уже примитивные части и только тогда, когда общий
  // делитель точно есть. По лемме Гаусса НОД собирается как содержимое × НОД
  // примитивных частей.
  const heu = heuristicGcd(p, q);
  if (heu) return primitivePart(P.mul(commonContent, heu));

  for (let step = 0; ; step++) {
    // Псевдоостатки — самая длинная петля движка: одного вызова хватает на
    // десятки секунд. Без проверки ВНУТРИ неё бюджет бесполезен — он сработал
    // бы только на следующем вызове НОДа, которого уже не случится.
    checkComputeBudget();
    if (q.isZero()) break;
    if (P.degreeIn(q, v) === 0) { p = P.constant(ONE); break; }
    // Страховка: даже когда общий делитель есть, промежуточные коэффициенты
    // растут как снежный ком. Сдаться здесь честно — вернём общий делитель,
    // который уже нашли, и он верен, просто, возможно, не наибольший.
    if (step >= PRS_MAX_STEPS || maxNorm(p) > PRS_MAX_COEFF || maxNorm(q) > PRS_MAX_COEFF) {
      return primitivePart(commonContent);
    }
    // Здесь стоит ПРИМИТИВНАЯ последовательность: каждый остаток делится на
    // своё содержимое. Это дорого — содержимое есть рекурсивный НОД всех
    // коэффициентов, и профиль показывает именно эти вложенные вызовы.
    //
    // Субрезультантная схема (делить на заранее известный g·h^δ вместо
    // содержимого) была написана и ОТКАЧЕНА: она давала неверный НОД, а неверный
    // НОД молча портит геометрию — это несравнимо хуже медленного счёта.
    // Подводных камней там больше, чем кажется: одного лишь приведения
    // псевдоостатка к стандартному виду не хватило. Браться за неё стоит
    // отдельно и с тестами на сам НОД, а не на его последствия.
    const r = pseudoRemainder(p, q, v);
    p = q;
    q = r.isZero() ? r : divideExact(r, contentInVar(r, v));
  }
  return primitivePart(P.mul(commonContent, p));
}

// ---- взаимная простота: дешёвая проверка вместо дорогой ------------------
//
// Классическая последовательность псевдоостатков раздувает коэффициенты
// экспоненциально: на многочлене девятой степени от трёх букв движок съедал всю
// память. Именно это, а не алгебра, мешало НАПИСАТЬ уравнение окружности —
// считалось оно быстро, а вставало на печати, потому что разложение на
// множители спрашивает НОД с производной.
//
// Хуже всего то, что в псевдоостатки попадал САМЫЙ ЧАСТЫЙ случай: НОД равен
// единице. Эвристика Char–Fortune–Watt распознать его не может в принципе —
// она обязана проверять ответ делением, а единица делит всё, и такой ответ
// отвергается как бесполезный.
//
// Проверяем по существу и дёшево: подставим числа вместо всех переменных, кроме
// главной, и посчитаем ОДНОМЕРНЫЙ НОД над полем. Любой общий делитель при
// подстановке остаётся общим делителем, поэтому нулевая степень одномерного
// НОДа означает нулевую степень настоящего. Обмануться можно только в другую
// сторону (подстановка обнулила старший коэффициент), поэтому берём две точки и
// верим только совпавшему ответу.
//
// Ошибка в любую сторону здесь безопасна: мы вернём общий делитель поменьше,
// то есть дробь окажется недосокращённой, но никогда не неверной.

// Точки подстановки фиксированы: случайность сделала бы печать одного и того же
// выражения то такой, то этакой.
const PROBE_POINTS = [
  [3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n, 43n, 47n, 53n, 59n, 61n],
  [2n, 9n, 4n, 25n, 6n, 49n, 8n, 15n, 10n, 21n, 12n, 33n, 14n, 35n, 16n, 39n, 18n],
];

// Многочлен как одномерный по переменной v: массив CFrac-коэффициентов,
// индекс — степень. Остальные переменные заменены числами.
function specialize(poly, v, point) {
  const out = [];
  for (const { exp, coeff } of poly.terms()) {
    let c = coeff;
    for (let i = 0; i < exp.length; i++) {
      if (i === v || !exp[i]) continue;
      const value = new CFrac(point[i % point.length]);
      for (let k = 0; k < exp[i]; k++) c = c.mul(value);
    }
    const e = exp[v] ?? 0;
    while (out.length <= e) out.push(ZERO);
    out[e] = out[e].add(c);
  }
  while (out.length > 0 && out[out.length - 1].isZero()) out.pop();
  return out;
}

// ---- проверка на взаимную простоту ПО МОДУЛЮ ------------------------------
//
// Раньше одномерный НОД считался над полем рациональных чисел, и это оказалось
// самым дорогим местом всего движка: профиль на реальной задаче показал 92%
// времени в Евклиде по целым, и все вызовы шли отсюда. Причина классическая —
// наивный Евклид над ℚ раздувает коэффициенты катастрофически: числа доходят до
// тысяч знаков, и каждое сокращение дроби идёт секундами.
//
// Но нам нужна не сама НОД, а только ответ «его степень нулевая». А степень
// можно считать в КОНЕЧНОМ поле, где числа не растут вовсе.
//
// Направление ошибки безопасное: приведение по модулю может степень НОДа только
// УВЕЛИЧИТЬ (на неудачном простом), но не уменьшить. Поэтому «степень ноль по
// модулю» гарантирует настоящую взаимную простоту, а «не ноль» просто отправляет
// на честный длинный путь — ровно как было.
//
// Простое взято ≡ 3 (mod 4): тогда x²+1 неприводим, и пары (re, im) образуют
// поле F_p², в котором живут наши гауссовы коэффициенты. Квадрат простого
// умещается в точные целые double, поэтому вся арифметика идёт на обычных
// числах без bigint.
const MOD = 1000003;
const MODn = BigInt(MOD);

const mAdd = (x, y) => [(x[0] + y[0]) % MOD, (x[1] + y[1]) % MOD];
const mSub = (x, y) => [(x[0] - y[0] + MOD) % MOD, (x[1] - y[1] + MOD) % MOD];
const mMul = (x, y) => [
  ((x[0] * y[0] - x[1] * y[1]) % MOD + MOD) % MOD,
  (x[0] * y[1] + x[1] * y[0]) % MOD,
];
const mIsZero = x => x[0] === 0 && x[1] === 0;

function mPow(base, exp) {
  let r = 1, b = base % MOD;
  while (exp > 0) {
    if (exp & 1) r = (r * b) % MOD;
    b = (b * b) % MOD;
    exp >>= 1;
  }
  return r;
}

// Обратный к ненулевому элементу F_p²: сопряжённое, делённое на норму. Норма
// нулю не равна никогда — ровно потому, что p ≡ 3 (mod 4).
function mInv(x) {
  const norm = ((x[0] * x[0] + x[1] * x[1]) % MOD + MOD) % MOD;
  if (norm === 0) return null;
  const inv = mPow(norm, MOD - 2);
  return [(x[0] * inv) % MOD, ((MOD - x[1]) % MOD * inv) % MOD];
}

// Дробь n/d по модулю. null, если знаменатель делится на простое — тогда это
// «плохое» простое, и проверку надо просто пропустить.
function fracMod(f) {
  const d = Number(((f.d % MODn) + MODn) % MODn);
  if (d === 0) return null;
  const n = Number(((f.n % MODn) + MODn) % MODn);
  return (n * mPow(d, MOD - 2)) % MOD;
}

// Подстановка чисел вместо всех переменных, кроме v, сразу в конечное поле:
// раздуваться тут нечему по построению.
function specializeMod(poly, v, point) {
  const out = [];
  for (const { exp, coeff } of poly.terms()) {
    const re = fracMod(coeff.re), im = fracMod(coeff.im);
    if (re === null || im === null) return null;
    let c = [re, im];
    for (let i = 0; i < exp.length; i++) {
      if (i === v || !exp[i]) continue;
      // Точки подстановки — bigint, а поле у нас на обычных числах.
      const raw = BigInt(point[i % point.length]);
      const value = [Number(((raw % MODn) + MODn) % MODn), 0];
      for (let k = 0; k < exp[i]; k++) c = mMul(c, value);
    }
    const e = exp[v] ?? 0;
    while (out.length <= e) out.push([0, 0]);
    out[e] = mAdd(out[e], c);
  }
  while (out.length > 0 && mIsZero(out[out.length - 1])) out.pop();
  return out;
}

function univariateRemMod(a, b) {
  const db = b.length - 1;
  const lead = mInv(b[db]);
  if (!lead) return null;
  const r = a.slice();
  while (r.length - 1 >= db && r.length > 0) {
    const factor = mMul(r[r.length - 1], lead);
    const shift = r.length - 1 - db;
    for (let i = 0; i <= db; i++) r[i + shift] = mSub(r[i + shift], mMul(factor, b[i]));
    while (r.length > 0 && mIsZero(r[r.length - 1])) r.pop();
  }
  return r;
}

function univariateGcdDegreeMod(a, b) {
  while (b.length > 0) {
    const r = univariateRemMod(a, b);
    if (r === null) return Infinity;
    [a, b] = [b, r];
  }
  return a.length - 1;
}

// Остаток от деления одномерных многочленов над полем.
function univariateRem(a, b) {
  const db = b.length - 1;
  let r = a.slice();
  for (let guard = 0; r.length - 1 >= db && r.length > 0; guard++) {
    if (guard > 64) return [];
    const factor = r[r.length - 1].div(b[db]);
    const shift = r.length - 1 - db;
    for (let i = 0; i <= db; i++) r[i + shift] = r[i + shift].sub(factor.mul(b[i]));
    while (r.length > 0 && r[r.length - 1].isZero()) r.pop();
  }
  return r;
}

function univariateGcdDegree(a, b) {
  for (let guard = 0; b.length > 0; guard++) {
    if (guard > 64) return Infinity;      // не сошлось — считаем, что не знаем
    [a, b] = [b, univariateRem(a, b)];
  }
  return a.length - 1;
}

// «Степень настоящего НОДа по переменной v равна нулю» — с той оговоркой выше.
function coprimeInVar(A, B, v) {
  for (const point of PROBE_POINTS) {
    const a = specializeMod(A, v, point);
    const b = specializeMod(B, v, point);
    if (a === null || b === null) continue;               // плохое простое — другая точка
    if (a.length === 0 || b.length === 0) return false;   // подстановка обнулила
    if (univariateGcdDegreeMod(a, b) !== 0) return false;
  }
  return true;
}

// ---- разложение на множители ---------------------------------------------

const MAX_DIVISOR_CANDIDATES = 256;

// Разложение на множители — украшение печати, а не арифметика: если оно не
// уложилось в бюджет, многочлен печатается развёрнутым, и всё остальное
// работает как ни в чём не бывало. Раньше бюджета не было, и на «некрасивой»
// окружности приложение просто вставало насмерть.
//
// Было 80 мс — столько выбиралось, когда НОД был в тридцать раз медленнее.
// После модулярного НОДа этого срока стало НЕ ХВАТАТЬ на пользу: у окружности
// через вершину и два основания чевиан знаменатель r² в 97 членов есть
// (4 члена)²·(4 члена)², и при 80 мс разложение обрывалось на полпути
// («4 · 4 · 16»), а при 200 мс доходит до конца. Расплата разовая: ответ
// кэшируется прямо на многочлене, поэтому цену платит первая отрисовка, а не
// каждое движение мыши.
const FACTOR_BUDGET_MS = 250;
let factorDeadline = Infinity;
const outOfBudget = () => Date.now() > factorDeadline;

// Одна строка панели зовёт разложение много раз подряд: числитель и знаменатель
// центра, его сопряжения, квадрата радиуса. Бюджет должен быть общим на всю
// строку, иначе полдюжины безнадёжных многочленов честно съедают по бюджету
// каждый, и перерисовка «некрасивой» окружности растягивается на полсекунды.
// Срок настраивается вызывающим, и это не прихоть: в барицентрике многочлены
// от трёх букв и высокой степени объективно крупнее комплексных, и 250 мс на
// всю строку там уходят в первую же координату — остальные печатаются длинной
// записью, хотя короткая существует и стоит ещё полсекунды.
export function withFactorBudget(fn, budgetMs = FACTOR_BUDGET_MS) {
  if (factorDeadline !== Infinity) return fn();     // бюджет уже открыт снаружи
  factorDeadline = Date.now() + budgetMs;
  try { return fn(); } finally { factorDeadline = Infinity; }
}

function derivative(poly, v) {
  const out = [];
  for (const { exp, coeff } of poly.terms()) {
    const e = exp[v] ?? 0;
    if (e === 0) continue;
    const next = exp.slice();
    next[v] = e - 1;
    out.push({ exp: next, coeff: coeff.mul(new CFrac(BigInt(e))) });
  }
  return P.fromTerms(out);
}

// Все делители многочлена — произведения подмножеств его неприводимых
// множителей, домноженные на единицы. Нужны для поиска линейных множителей
// по теореме о рациональных корнях.
function divisorsOf(poly, budget) {
  const { factors } = factorPoly(poly);
  let list = [P.constant(ONE)];
  for (const { poly: f, power } of factors) {
    const grown = [];
    for (const d of list) {
      let acc = d;
      grown.push(acc);
      for (let k = 0; k < power; k++) { acc = P.mul(acc, f); grown.push(acc); }
    }
    list = grown;
    if (list.length > budget) return list.slice(0, budget);
  }
  const units = [P.constant(ONE), P.constant(new CFrac(-1n)), P.constant(new CFrac(0n, 1n)),
    P.constant(new CFrac(0n, -1n))];
  const out = [];
  for (const d of list) for (const u of units) out.push(P.mul(d, u));
  return out.slice(0, budget);
}

// Ищет множитель вида (α·x_v − β): α делит старший коэффициент, β — младший.
function findLinearFactor(poly, v) {
  const cs = P.coeffsIn(poly, v);
  const d = cs.length - 1;
  const trailing = cs.find(c => !c.isZero());
  if (!trailing) return null;
  const alphas = divisorsOf(cs[d], MAX_DIVISOR_CANDIDATES);
  const betas = divisorsOf(trailing, MAX_DIVISOR_CANDIDATES);
  const xv = P.variable(v);
  let tried = 0;
  for (const alpha of alphas) {
    for (const beta of betas) {
      if (++tried > MAX_DIVISOR_CANDIDATES * 4) return null;
      const candidate = P.sub(P.mul(alpha, xv), beta);
      if (P.degreeIn(candidate, v) !== 1) continue;
      const quotient = divideExact(poly, candidate);
      if (quotient) return { factor: primitivePart(candidate), quotient };
    }
  }
  return null;
}

function pushFactor(map, poly, power = 1) {
  if (P.isOne(poly)) return;
  const key = P.terms(poly).map(t => `${t.exp.join(',')}:${t.coeff.toString()}`).sort().join('|');
  const cur = map.get(key);
  if (cur) cur.power += power;
  else map.set(key, { poly, power });
}

// Выше этого размера не запускается ДОРОГОЙ поиск множителя (перебор «столбиком»
// в findLinearFactor). Он стоит настоящих миллисекунд на каждой перерисовке и
// отбирает время у соседнего многочлена, который разложился бы отлично: ровно
// так у «некрасивой» окружности огромный r² съедал бюджет, а красивый центр
// из-за этого печатался развёрнутым.
//
// А вот ДЕШЁВЫЕ шаги — одночлены, содержимое, кратные множители через НОД с
// производной — идут при любом размере, и это принципиально. Раньше отсечка
// стояла на входе и глушила их заодно, а замер показал, что теряется настоящее:
// у окружности через вершину и два основания чевиан знаменатель r² в 97 членов
// есть ПОЛНЫЙ КВАДРАТ 16-членного, находится это одним НОДом за 128 мс — и всё
// равно печаталось развёрнутым, только потому что 97 > 30. Соседний числитель в
// 147 членов при этом честно неприводим, и дешёвые шаги отвечают это быстро,
// тогда как дорогой перебор тратил на тот же ответ 4.2 секунды.
const FACTOR_MAX_TERMS = 30;

function factorInto(poly, map) {
  if (P.isOne(poly)) return;
  const v = mainVar(poly);
  if (v < 0) return;                                   // константа: ушла в content
  if (outOfBudget()) { pushFactor(map, poly); return; }

  // одночленные множители x_v^k
  const minDeg = Math.min(...P.terms(poly).map(t => t.exp[v] ?? 0));
  if (minDeg > 0) {
    pushFactor(map, P.variable(v), minDeg);
    factorInto(divideExact(poly, P.pow(P.variable(v), minDeg)), map);
    return;
  }

  // содержимое по старшей переменной
  const cont = contentInVar(poly, v);
  if (!P.isOne(cont)) {
    factorInto(cont, map);
    factorInto(divideExact(poly, cont), map);
    return;
  }

  const deg = P.degreeIn(poly, v);
  // Примитивный и линейный по переменной ⟹ неприводим: любой разложение
  // потребовало бы множителя нулевой степени по v, а он ушёл бы в содержимое.
  if (deg <= 1) { pushFactor(map, poly); return; }

  // кратные множители: НОД с производной
  const g = polyGcd(poly, derivative(poly, v));
  if (P.degreeIn(g, v) > 0) {
    factorInto(g, map);
    factorInto(divideExact(poly, g), map);
    return;
  }

  // Дальше — единственный дорогой шаг, и вот он уже под ограничением по размеру.
  if (poly.size > FACTOR_MAX_TERMS) { pushFactor(map, poly); return; }

  const linear = findLinearFactor(poly, v);
  if (linear) {
    factorInto(linear.factor, map);
    factorInto(linear.quotient, map);
    return;
  }

  // Дальше нужен настоящий многомерный факторизатор (подъём Гензеля);
  // см. README — честно оставляем как есть.
  pushFactor(map, poly);
}

const isRealPoly = poly => P.terms(poly).every(t => t.coeff.im.isZero());

// У ВЕЩЕСТВЕННОГО многочлена комплексных множителей быть не должно.
//
// Коэффициенты здесь живут в Q(i), поэтому разложение честно распадается и там,
// где на бумаге никто так не пишет: x² + y² превращается в (x + iy)(x − iy).
// Компланатору такое иногда осмысленно, а в барицентрике буквы — длины сторон,
// и мнимая единица в ответе выглядит поломкой. Она ею и выглядела: окружность
// через две сопряжённые точки и вершину печаталась с i, хотя сама была
// вещественной.
//
// Лечение ничего не теряет: у вещественного многочлена комплексные множители
// идут сопряжёнными парами, поэтому их произведение снова вещественно.
// Вещественные множители остаются разложенными — (a−b)(a²+b²) так и печатается,
// — а всё остальное собирается обратно в один множитель ТОЧНЫМ ДЕЛЕНИЕМ.
// Делением, а не перемножением: комплексная единица может сидеть и в
// содержимом (canonicalUnit домножает его на i, чтобы зафиксировать выбор), и
// тогда перемножение множителей дало бы не тот ответ.
function realParts(poly, content, factors) {
  if (!isRealPoly(poly)) return { content, factors };
  if (content.im.isZero() && factors.every(f => isRealPoly(f.poly))) {
    return { content, factors };
  }
  const real = factors.filter(f => isRealPoly(f.poly));
  // Остаток берётся ТОЧНЫМ ДЕЛЕНИЕМ, а не перемножением оставшихся множителей.
  // Перемножить было бы дешевле, но неверно: разложение восстанавливает
  // исходный многочлен лишь С ТОЧНОСТЬЮ ДО ЕДИНИЦЫ (±1, ±i), которую
  // canonicalUnit прячет в выбор представителей. На нашем примере произведение
  // двух комплексных множителей давало ровно i·(нужное), и «вещественная»
  // проверка честно отвергала результат — а печать оставалась с i.
  let known = P.constant(ONE);
  for (const { poly: f, power } of real) known = P.mul(known, P.pow(f, power));
  const rest = divideExact(poly, known);
  if (!rest) return { content, factors };
  const split = contentAndPrimitive(rest);
  if (!split.content.im.isZero() || !isRealPoly(split.primitive)) return { content, factors };
  const tail = P.isOne(split.primitive) ? [] : [{ poly: split.primitive, power: 1 }];
  return { content: split.content, factors: [...real, ...tail] };
}

export function factorPoly(poly) {
  if (poly.isZero()) return { content: ZERO, factors: [] };
  // Разложение зовётся из печати, а её дёргают на каждой перерисовке строки —
  // кэшируем прямо на объекте (многочлены неизменяемы).
  if (poly._factored) return poly._factored;
  const { content, primitive } = contentAndPrimitive(poly);
  const map = new Map();
  // Бюджет общий на всё дерево вызовов, но заводит его только самый верхний:
  // делители ищутся через рекурсивный factorPoly, и вложенный вызов не вправе
  // продлевать себе время.
  const outermost = factorDeadline === Infinity;
  if (outermost) factorDeadline = Date.now() + FACTOR_BUDGET_MS;
  try {
    factorInto(primitive, map);
  } finally {
    if (outermost) factorDeadline = Infinity;
  }
  // Порядок множителей должен быть каноническим, иначе одно и то же выражение
  // печаталось бы то как «b c», то как «c b».
  const totalDeg = p => Math.max(0, ...P.terms(p).map(t => t.exp.reduce((s, e) => s + e, 0)));
  const leadExp = p => P.terms(p).reduce((best, t) => (best === null || P.compareExp(t.exp, best) < 0 ? t.exp : best), null) ?? [];
  const factors = [...map.values()].sort((x, y) =>
    totalDeg(x.poly) - totalDeg(y.poly)
    || P.terms(x.poly).length - P.terms(y.poly).length
    || P.compareExp(leadExp(x.poly), leadExp(y.poly)));
  const result = realParts(poly, content, factors);
  poly._factored = result;
  return result;
}

// ---- точный квадратный корень --------------------------------------------
//
// Геометрия иногда просит РАДИУС, а движок хранит его квадрат — сам радиус
// иррационален. Но не всегда: центр гомотетии двух окружностей выражается через
// произведение r₁·r₂, а оно сплошь и рядом рационально даже тогда, когда каждый
// радиус по отдельности — нет (r₁² = 2, r₂² = 8 ⟹ r₁r₂ = 4). Поэтому вместо
// «радикалов не бывает» здесь честная попытка: получилось — считаем точно,
// не получилось — говорим прямо.
//
// Ответ ВСЕГДА проверяется возведением в квадрат, так что неверный сюда физически
// не проходит — та же дисциплина, что у эвристического НОДа.

// Целочисленный корень: Ньютон по bigint, точный.
function isqrt(n) {
  if (n < 0n) return null;
  if (n < 2n) return n;
  let x = n, y = (x + 1n) / 2n;
  while (y < x) { x = y; y = (x + n / x) / 2n; }
  return x * x === n ? x : null;
}

function sqrtFraction(f) {
  const n = isqrt(f.n < 0n ? -f.n : f.n);
  const d = isqrt(f.d);
  if (n === null || d === null || f.n < 0n) return null;
  return new Fraction(n, d);
}

// Корень из гауссова рационального. Ноль и вещественные неотрицательные — свои
// очевидные случаи; у отрицательных корень чисто мнимый (i в поле есть);
// в общем случае решаем (u+vi)² = z обычным способом через модуль.
export function sqrtCFrac(z) {
  if (z.re.isZero() && z.im.isZero()) return new CFrac(0n, 0n);
  if (z.im.isZero()) {
    const positive = sqrtFraction(z.re);
    if (positive) return new CFrac(positive, 0n);
    const negated = sqrtFraction(z.re.neg());
    return negated ? new CFrac(0n, negated) : null;
  }
  // |z| обязан быть рациональным, иначе корень выходит за пределы Q(i)
  const abs = sqrtFraction(z.re.mul(z.re).add(z.im.mul(z.im)));
  if (!abs) return null;
  const u = sqrtFraction(z.re.add(abs).div(new Fraction(2n)));
  if (!u || u.isZero()) return null;
  const v = z.im.div(u.mul(new Fraction(2n)));
  return new CFrac(u, v);
}

// Корень из многочлена «столбиком» по главной переменной: старший коэффициент
// извлекается рекурсивно, остальные восстанавливаются по одному из уже
// найденных. null, если корня в кольце нет.
// Точки для дешёвого отсева. Взяты фиксированными, а не случайными, чтобы
// поведение было воспроизводимым: отладка «иногда быстро, иногда нет» — худшее,
// что можно устроить.
const PROBE = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n];

// Дешёвый отсев перед дорогим «столбиком».
//
// Квадрат многочлена в ЛЮБОЙ точке даёт квадрат числа, поэтому «не квадрат в
// точке» ⟹ «не квадрат вообще». Ошибиться можно только в другую сторону —
// случайно попасть в квадрат, — и это безопасно: тогда просто отработает
// честный столбик и вернёт null сам.
//
// Ради чего: на разложимость проверяется КАЖДОЕ квадратное уравнение, и почти
// всегда ответ «не квадрат». Без отсева на это уходило всё время: столбик
// честно перебирал коэффициенты и сдавался в самом конце.
function looksLikeSquare(poly) {
  const values = [];
  for (let v = 0; v < 64; v++) values.push(new CFrac(PROBE[v % PROBE.length] + BigInt(v)));
  let value;
  try { value = P.evalPoly(poly, values); } catch { return true; }
  if (value.re.isZero() && value.im.isZero()) return true;   // ноль ничего не говорит
  return !!sqrtCFrac(value);
}

export function polySqrt(poly) {
  if (poly.isZero()) return P.zero();
  if (!looksLikeSquare(poly)) return null;
  return sqrtByLongDivision(poly);
}

function sqrtByLongDivision(poly) {
  if (poly.isZero()) return P.zero();

  const v = mainVar(poly);
  if (v < 0) {
    const c = sqrtCFrac(P.leadingCoeff(poly));
    return c ? P.constant(c) : null;
  }

  const c = P.coeffsIn(poly, v);
  const degree = c.length - 1;
  if (degree % 2 !== 0) return null;            // нечётная степень — не квадрат
  const n = degree / 2;

  const lead = sqrtByLongDivision(c[degree]);
  if (!lead) return null;

  const d = new Array(n + 1).fill(null).map(() => P.zero());
  d[n] = lead;
  const twoLead = P.mul(P.constant(new CFrac(2n)), lead);

  // Коэффициент квадрата при v^m — это Σ d_i·d_j по i+j = m. Идём по убыванию
  // m: единственное неизвестное в такой сумме — d_{n−k}, оно стоит в паре с
  // d_n, всё остальное уже найдено.
  for (let k = 1; k <= n; k++) {
    const m = 2 * n - k;
    let known = P.zero();
    for (let i = Math.max(0, m - n); i <= n; i++) {
      const j = m - i;
      if (j < 0 || j > n) continue;
      if (i <= n - k || j <= n - k) continue;   // это и есть неизвестное слагаемое
      known = P.add(known, P.mul(d[i], d[j]));
    }
    const rest = divideExact(P.sub(c[m] ?? P.zero(), known), twoLead);
    if (!rest) return null;
    d[n - k] = rest;
  }

  let root = P.zero();
  const x = P.variable(v);
  for (let j = 0; j <= n; j++) root = P.add(root, P.mul(d[j], P.pow(x, j)));

  // Проверка обязательна: «столбик» молча пропустил бы младшие члены, которые
  // в квадрат не укладываются.
  return P.equals(P.mul(root, root), poly) ? root : null;
}

// Бюджет живёт в отдельном модуле (budget.js): проверять его надо и в самом
// низу, в умножении многочленов, а низ ни от чего зависеть не должен.
export { BudgetExceeded, withComputeBudget, noteSize, lastPeak, checkComputeBudget };
