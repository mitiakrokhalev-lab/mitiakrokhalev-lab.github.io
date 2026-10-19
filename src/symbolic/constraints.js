import { Ring } from './ring.js';
import { Rational } from './rational.js';
import { det } from './conic.js';
import * as P from './poly.js';
import { ONE } from './complex-fraction.js';
import { solveQuadratic } from './quadratic.js';
import { baseRingOf, QuadraticExt } from './quadratic-ext.js';
import { parseExpression, namesIn, evalAst } from './expression.js';

// Командный ввод: пользователь пишет условия на точки, движок решает систему.
//
// Зачем: достроить, скажем, подобный треугольник мышью — это десяток
// вспомогательных объектов, каждый из которых движку надо осмыслить. Условие
// similar(A,B,C,P,Q,X) описывает ту же точку одной строкой.
//
// Аргумент команды — не имя точки, а ВЫРАЖЕНИЕ: perpen(A, P, Q+A/3, X) законно.
// Иначе на каждую «середину чего-нибудь» и каждую вершину педального
// треугольника приходилось бы заводить отдельную точку, хотя в условие она
// входит один раз. Имена, встретившиеся в выражениях, и есть точки строки;
// те из них, которых ещё нет на чертеже, — неизвестные.
//
// Каждая команда возвращает АЛГЕБРАИЧЕСКОЕ РАВЕНСТВО (или несколько),
// эквивалентное её геометрическому смыслу. Равенства бывают двух сортов, и это
// определяет всю конструкцию:
//
//   * «комплексные» (similar, vectors, harm) — без сопряжений. Такое равенство
//     это ДВА вещественных условия, оно фиксирует точку целиком.
//   * «вещественные» (angle, cocycl, paral, perpen, collinear, anglesum) — вида
//     A·B̄ − Ā·B = 0, то есть «отношение вещественно». Само выражение чисто
//     мнимое, поэтому равенство даёт ОДНО вещественное условие: точка остаётся
//     на прямой или окружности, но не фиксируется.
//
// Отсюда счёт: k неизвестных точек — это 2k вещественных степеней свободы, и
// нужно ровно 2k независимых условий.
//
// Особняком стоят команды-ПОСТРОЕНИЯ (buildpoint, buildline, radline): они не
// накладывают условий, а просто рисуют объект по готовому выражению. Систему с
// ними не составишь, поэтому в одной строке с условиями они не встречаются —
// это проверяется при разборе.

// A·B̄ − Ā·B: чисто мнимое, ноль ⟺ A/B вещественно.
const ratioIsReal = (A, B) => A.mul(B.conjugate()).sub(A.conjugate().mul(B));

// A·B̄ + Ā·B: вещественное, ноль ⟺ A/B чисто мнимое.
const ratioIsImaginary = (A, B) => A.mul(B.conjugate()).add(A.conjugate().mul(B));

export const COMMANDS = {
  // X1X2X3 подобен X4X5X6 с той же ориентацией:
  // (x3−x1)/(x2−x1) = (x6−x4)/(x5−x4)
  similar: {
    arity: 6,
    kind: 'complex',
    describe: 'подобие треугольников с сохранением ориентации',
    build: ([p, q, r, u, v, w]) => r.sub(p).mul(v.sub(u)).sub(w.sub(u).mul(q.sub(p))),
  },

  // Шесть точек: равенство направленных углов X1X2X3 и X4X5X6 (по модулю 180°),
  // то есть отношение (x1−x2)/(x3−x2) : (x4−x5)/(x6−x5) вещественно.
  //
  // Четыре аргумента: угол ABC равен arg(D). Второй угол здесь задан не тремя
  // точками, а ГОТОВЫМ направлением — комплексным числом. Условие то же самое:
  // (A−B)/((C−B)·D) вещественно.
  //
  // Смысл имеет любое D ≠ 0, но задумано оно единичным: тогда D — это чистое
  // направление, и вместе с `unity(n)` получается «угол ABC равен k·360/n»
  // одной строкой: angle(A, B, C, unity(6)).
  //
  // Как и все углы в движке, этот — направленный и по модулю 180°.
  angle: {
    arity: 6,
    arities: [6, 4],
    kind: 'real',
    describe: 'равенство направленных углов (или угол по заданному направлению)',
    checkArity: n => (n === 6 || n === 4 ? null
      : 'нужно шесть точек (два угла) либо четыре (три точки и направление)'),
    build: values => (values.length === 6
      ? ratioIsReal(values[0].sub(values[1]).mul(values[5].sub(values[4])),
                    values[2].sub(values[1]).mul(values[3].sub(values[4])))
      : ratioIsReal(values[0].sub(values[1]), values[2].sub(values[1]).mul(values[3]))),
  },

  // Знакопеременная сумма направленных углов равна нулю (по модулю 180°).
  // Направленный угол X1X2X3 — это arg((x1−x2)/(x3−x2)), поэтому «сумма углов
  // равна нулю» — это «произведение отношений вещественно», и никакой
  // тригонометрии не нужно. Знак у слагаемого переворачивает его отношение.
  anglesum: {
    arity: null,
    kind: 'real',
    describe: 'знакопеременная сумма направленных углов равна нулю',
    checkArity: n => (n >= 4 && n % 4 === 0
      ? null : 'аргументы идут четвёрками «знак, X1, X2, X3»'),
    build: (values, command) => {
      let num = null;
      let den = null;
      command.signs.forEach((sign, k) => {
        const [p, q, r] = values.slice(3 * k, 3 * k + 3);
        const top = p.sub(q);
        const bottom = r.sub(q);
        if (top.isZero() || bottom.isZero()) {
          throw new Error(`anglesum: угол №${k + 1} вырожден — вершина совпала со стороной`);
        }
        const [n, d] = sign > 0 ? [top, bottom] : [bottom, top];
        num = num ? num.mul(n) : n;
        den = den ? den.mul(d) : d;
      });
      return ratioIsReal(num, den);
    },
  },

  // Векторы X1X2 и X3X4 равны.
  vectors: {
    arity: 4,
    kind: 'complex',
    describe: 'равенство векторов',
    build: ([p, q, r, s]) => q.sub(p).sub(s.sub(r)),
  },

  // X1X2X3X4 вписанный: двойное отношение вещественно.
  cocycl: {
    arity: 4,
    kind: 'real',
    describe: 'четыре точки на одной окружности (или прямой)',
    build: ([p, q, r, s]) => ratioIsReal(p.sub(r).mul(q.sub(s)), p.sub(s).mul(q.sub(r))),
  },

  // Шесть точек на одной конике.
  //
  // Определитель 6×6 из строк (z², z z̄, z̄², z, z̄, 1) обращается в ноль ровно
  // тогда, когда через шесть точек проходит коника. Условие ОДНО вещественное,
  // а не два: сопряжение переставляет столбцы парами (z²↔z̄², z↔z̄), это чётная
  // перестановка, поэтому определитель равен своему сопряжённому — то есть он
  // веществен сам по себе.
  conconic: {
    arity: 6,
    kind: 'real',
    describe: 'шесть точек на одной конике',
    build: pts => det(pts.map(z => {
      const zc = z.conjugate();
      return [z.mul(z), z.mul(zc), zc.mul(zc), z, zc, z.ring.one()];
    }), pts[0].ring),
  },

  paral: {
    arity: 4,
    kind: 'real',
    describe: 'параллельность',
    build: ([p, q, r, s]) => ratioIsReal(q.sub(p), s.sub(r)),
  },

  perpen: {
    arity: 4,
    kind: 'real',
    describe: 'перпендикулярность',
    build: ([p, q, r, s]) => ratioIsImaginary(q.sub(p), s.sub(r)),
  },

  // Ортоцентрическая четвёрка: каждая точка — ортоцентр трёх остальных.
  // Достаточно двух перпендикулярностей: X1X2 ⟂ X3X4 и X1X3 ⟂ X2X4, третья
  // (X1X4 ⟂ X2X3) из них уже следует. Два вещественных условия — ровно столько,
  // сколько стоит одна неизвестная точка.
  krokhalyator: {
    arity: 4,
    // Три точки — построить четвёртую, четыре — потребовать, чтобы четвёрка
    // была ортоцентрической. Это одно и то же утверждение с разных сторон, и
    // разводить его по двум именам было бы враньём про то, что это разные вещи.
    checkArity: n => (n === 3 || n === 4 ? null
      : 'ожидалось 3 точки (построить четвёртую) или 4 (условие на четвёрку)'),
    kindOf: n => (n === 3 ? 'build' : 'real'),
    named: true,
    kind: 'real',
    describe: 'ортоцентрическая четвёрка; с тремя точками — построение четвёртой',
    build: ([p, q, r, s]) => [
      ratioIsImaginary(q.sub(p), s.sub(r)),
      ratioIsImaginary(r.sub(p), s.sub(q)),
    ],
  },

  // [X1X2, X3X4] = −1, то есть (x3−x1)(x4−x2) + (x3−x2)(x4−x1) = 0.
  harm: {
    arity: 4,
    kind: 'complex',
    describe: 'гармоническая четвёрка',
    build: ([p, q, r, s]) => r.sub(p).mul(s.sub(q)).add(r.sub(q).mul(s.sub(p))),
  },

  collinear: {
    arity: 3,
    kind: 'real',
    describe: 'три точки на одной прямой',
    build: ([p, q, r]) => ratioIsReal(q.sub(p), r.sub(p)),
  },

  // ---- построения, а не условия -------------------------------------------

  buildpoint: {
    arity: 1,
    kind: 'build',
    describe: 'построить точку по выражению',
    named: true,          // допускает запись buildpoint(имя = выражение)
  },

  // ---- готовые построения планиметрии --------------------------------------
  //
  // Всё это выражается и через buildpoint, но записывать каждый раз формулу —
  // значит каждый раз её и выводить. Команда называет вещь своим именем.

  isogonal: {
    arity: 1,
    kind: 'build',
    named: true,
    describe: 'изогонально сопряжённая точка относительно треугольника ABC',
  },

  segcircle: {
    arity: 3, kind: 'build', named: true,
    describe: 'окружности, вписанные в сегмент хорды X2X3 и касающиеся дуги в X1'
      + ' (их две — по одной в каждый сегмент)',
  },

  semiincircle: {
    arity: 0,
    checkArity: n => (n === 0 ? null
      : 'аргументов не нужно: полувписанная берётся в угле A треугольника ABC'),
    kind: 'build', named: true,
    describe: 'полувписанная окружность в угле A: касается AB, AC и описанной изнутри',
  },

  rot90: {
    arity: 2,
    checkArity: n => (n === 1 || n === 2 ? null : 'ожидалась точка и (необязательно) центр'),
    kind: 'build',
    named: true,
    describe: 'поворот точки на 90° вокруг центра (без центра — вокруг центра описанной)',
  },

  rot60: {
    arity: 2,
    checkArity: n => (n === 1 || n === 2 ? null : 'ожидалась точка и (необязательно) центр'),
    kind: 'build',
    named: true,
    describe: 'поворот точки на 60° вокруг центра (без центра — вокруг центра описанной)',
  },

  incenter: {
    arity: 0,
    checkArity: n => (n === 0 ? null : 'аргументов не нужно: инцентр берётся у треугольника ABC'),
    kind: 'build',
    named: true,
    describe: 'инцентр треугольника ABC',
  },

  buildline: {
    arity: 3,
    kind: 'build',
    describe: 'построить прямую по уравнению A·z + B·z̄ + C = 0',
    named: true,
  },

  radline: {
    arity: 2,
    kind: 'build',
    describe: 'построить радикальную ось двух окружностей (точка = окружность нулевого радиуса)',
    named: true,
  },

  // Центры гомотетии двух окружностей — внешний и внутренний. Радиуса у движка
  // нет (он иррационален), но он и не нужен: после избавления от знаменателя
  // остаётся единственный корень — произведение радиусов, а оно рационально
  // заметно чаще, чем каждый радиус по отдельности.
  homothety: {
    arity: 2,
    kind: 'build',
    describe: 'центры гомотетии двух окружностей (внешний и внутренний)',
    named: true,
  },

  // Пересечение двух объектов панели, посчитанное НАМИ.
  //
  // Казалось бы, зачем: пересечение и так можно отметить мышью. Затем, что на
  // длинных построениях GeoGebra встаёт, вычисляя его сама, — и вешает вкладку
  // ещё до того, как наш код получит управление. Своя команда обходит её
  // целиком: ответ считает движок, а рисование можно и выключить.
  meet: {
    arity: 2,
    kind: 'build',
    describe: 'пересечение двух объектов панели, посчитанное движком',
    named: true,
  },

  // Циркуль из GeoGebra: раствор по отрезку AB, ножка в C. Радикала не требует
  // (см. CircleEq.compass): окружность хранится квадратом радиуса, а он
  // рационален.
  compass: {
    arity: 3,
    kind: 'build',
    describe: 'окружность с центром в X3 и радиусом X1X2',
    named: true,
  },

  // Касательные из точки к окружности. Точки касания — это пересечение ПОЛЯРЫ
  // точки с самой окружностью, а касательная в точке касания — снова поляра,
  // только уже этой точки.
  tangent: {
    arity: 2,
    kind: 'build',
    describe: 'касательные из точки к окружности',
    named: true,
  },

  // ---- коники ---------------------------------------------------------------
  //
  // Коника хранится шестью коэффициентами и, в отличие от окружности, своей
  // буквой на панели. Строится тремя способами — по пяти точкам, по фокусу с
  // директрисой и по двум фокусам с точкой, — а дальше живёт как обычный объект:
  // поляра, центр, принадлежность точки.
  conic5: {
    arity: 5,
    kind: 'build',
    named: true,
    describe: 'коника через пять точек',
  },

  parabola: {
    arity: 2,
    kind: 'build',
    named: true,
    describe: 'парабола по фокусу и директрисе',
  },

  conic: {
    arity: 3,
    kind: 'build',
    named: true,
    describe: 'коника по двум фокусам и точке на ней (эллипс или гипербола)',
  },

  centre: {
    arity: 1,
    kind: 'build',
    named: true,
    describe: 'центр коники',
  },

  polar: {
    arity: 2,
    kind: 'build',
    named: true,
    describe: 'поляра точки относительно коники или окружности',
  },

  commontangent: {
    arity: 2,
    kind: 'build',
    describe: 'общие касательные двух окружностей (и их центры гомотетии)',
    named: true,
  },
};

// ---- разбор ---------------------------------------------------------------

// Разбиение по запятым ВЕРХНЕГО уровня: внутри аргумента теперь бывают и
// скобки, и запятые (distance(P, f)), так что простым split не обойтись.
function splitTopLevel(source) {
  const out = [];
  let depth = 0;
  let cur = '';
  for (const ch of source) {
    if (ch === '(' || ch === '[') depth++;
    else if (ch === ')' || ch === ']') depth--;
    if (ch === ',' && depth === 0) { out.push(cur); cur = ''; continue; }
    cur += ch;
  }
  out.push(cur);
  return out.map(x => x.trim()).filter(x => x !== '');
}

// Раньше аргументы разделялись «запятыми ИЛИ пробелами», и старые записи вроде
// similar(A B C B C X) до сих пор встречаются в заметках. Теперь пробел — часть
// выражения, поэтому по пробелам режем только когда запятых нет вовсе, кусков
// получается ровно столько, сколько нужно, и все они — голые имена.
function splitArgs(inner, spec) {
  const byComma = splitTopLevel(inner);
  if (byComma.length > 1 || spec.arity === 1 || spec.arity === null) return byComma;
  const bySpace = inner.trim().split(/\s+/).filter(Boolean);
  const bare = bySpace.every(x => /^[A-Za-zА-Яа-я_][A-Za-zА-Яа-я0-9_']*$/.test(x));
  // У команды может быть несколько допустимых длин (angle — шесть точек или
  // четыре аргумента), тогда старая запись через пробелы годится для каждой.
  const allowed = spec.arities ?? [spec.arity];
  return allowed.includes(bySpace.length) && bare ? bySpace : byComma;
}

const LABELLED = /^\s*([A-Za-zА-Яа-я_][A-Za-zА-Яа-я0-9_']*)\s*=([^=].*)$/s;

// Вид команды: у большинства он один на все случаи, но у krokhalyator зависит
// от числа аргументов — три точки строят, четыре утверждают.
export const kindOf = command =>
  command.spec.kindOf ? command.spec.kindOf(command.args.length) : command.spec.kind;

// Разбирает аргументы одной команды в деревья выражений. Возвращает готовую
// команду; всё, что специфично для команды (знаки у anglesum, имя у построений),
// откладывается в её поля.
function readArgs(name, spec, chunks) {
  const command = { name, spec, args: [], signs: null, label: null };
  let list = chunks;

  // Построения можно называть: buildpoint(M1 = (P+Q)/2). Без имени точка
  // получит его сама, но тогда его не подставишь в следующую строку.
  if (spec.named && list.length > 0) {
    const m = LABELLED.exec(list[0]);
    if (m) {
      command.label = m[1];
      list = [m[2].trim(), ...list.slice(1)];
    }
  }

  // У anglesum четвёрки «знак, X1, X2, X3»: знаки идут отдельными аргументами.
  if (name === 'anglesum') {
    const signs = [];
    const points = [];
    for (let i = 0; i < list.length; i += 4) {
      const sign = list[i];
      if (sign !== '+' && sign !== '-') {
        throw new Error(`anglesum: на месте ${i + 1}-го аргумента ожидался знак + или −, а там «${sign}»`);
      }
      signs.push(sign === '+' ? 1 : -1);
      points.push(list[i + 1], list[i + 2], list[i + 3]);
    }
    command.signs = signs;
    list = points;
  }

  const expected = spec.arity;
  if (spec.checkArity) {
    const complaint = spec.checkArity(chunks.length);
    if (complaint) throw new Error(`${name}: ${complaint}, получено ${chunks.length}`);
  } else if (list.length !== expected) {
    throw new Error(`${name}: ожидалось аргументов — ${expected}, получено ${list.length}`);
  }

  command.args = list.map(chunk => {
    try { return parseExpression(chunk); }
    catch (e) { throw new Error(`${name}, аргумент «${chunk}»: ${e.message}`); }
  });
  return command;
}

// Находит вызовы вида имя(аргументы) с учётом вложенных скобок.
export function parseLine(text) {
  const commands = [];
  const source = String(text ?? '');
  let i = 0;
  while (i < source.length) {
    const rest = source.slice(i);
    const head = rest.match(/^\s*([A-Za-zА-Яа-я][A-Za-zА-Яа-я0-9_]*)\s*\(/);
    if (!head) {
      if (/^\s*[;,]?\s*$/.test(rest)) break;
      const stray = rest.trim().split(/\s+/)[0];
      throw new Error(`не похоже на команду: «${stray}»`);
    }
    let depth = 0;
    let j = i + head[0].length - 1;
    for (; j < source.length; j++) {
      if (source[j] === '(') depth++;
      else if (source[j] === ')') { depth--; if (depth === 0) break; }
    }
    if (depth !== 0) throw new Error(`не закрыта скобка в «${head[1]}(...»`);
    const inner = source.slice(i + head[0].length, j);
    const name = head[1].toLowerCase();
    const spec = COMMANDS[name];
    if (!spec) {
      throw new Error(`неизвестная команда «${head[1]}»; есть: ${Object.keys(COMMANDS).join(', ')}`);
    }
    const command = readArgs(name, spec, splitArgs(inner, spec));
    command.source = source.slice(i, j + 1).trim();
    commands.push(command);
    i = j + 1;
    const sep = source.slice(i).match(/^\s*[;,]?\s*/);
    i += sep ? sep[0].length : 0;
  }
  if (commands.length === 0) throw new Error('пустая строка');

  // Построение ничего не утверждает про точку, поэтому в систему его не
  // возьмёшь: смешивать их с условиями бессмысленно, и молчать об этом хуже,
  // чем сказать сразу.
  const builds = commands.filter(c => kindOf(c) === 'build');
  if (builds.length > 0 && builds.length !== commands.length) {
    throw new Error(`${builds[0].name} — это построение, а не условие; в одной строке с условиями оно не работает`);
  }
  return commands;
}

// Каждая непустая строка — отдельная система.
export function parseProgram(text) {
  return String(text ?? '')
    .split('\n')
    .map((line, index) => ({ index, source: line }))
    .filter(x => x.source.trim() && !x.source.trim().startsWith('#'))
    .map(x => {
      try { return { ...x, commands: parseLine(x.source) }; }
      catch (e) { return { ...x, error: e.message }; }
    });
}

// ---- линейная алгебра над полем рациональных функций ---------------------

// Раскладывает многочлен на свободный член и коэффициенты при неизвестных.
// null, если по неизвестным он не линеен — «нелинейную фигню» решать не беремся.
function linearParts(poly, unknownIndices) {
  const isUnknown = new Set(unknownIndices);
  const coeffs = new Map();
  const constTerms = [];
  for (const { exp, coeff } of poly.terms()) {
    let hit = -1;
    let degree = 0;
    for (let v = 0; v < exp.length; v++) {
      if (!isUnknown.has(v) || exp[v] === 0) continue;
      degree += exp[v];
      hit = v;
    }
    if (degree === 0) { constTerms.push({ exp, coeff }); continue; }
    if (degree > 1) return null;
    const stripped = exp.slice();
    stripped[hit] = 0;
    if (!coeffs.has(hit)) coeffs.set(hit, []);
    coeffs.get(hit).push({ exp: stripped, coeff });
  }
  return { coeffs, constTerms };
}

// Метод Гаусса над Rational. Возвращает решение, либо описание того, почему
// его нет: система вырождена (бесконечно много решений) или несовместна.
// unknownCount передаётся отдельно, потому что при ПУСТОМ наборе строк вывести
// его из самих строк неоткуда. Раньше он в этом случае считался нулём, и система
// без единого уравнения объявлялась решённой — а пользователь, написавший одно
// условие окружности, получал «линейных условий уже достаточно» вместо честного
// «условий не хватает».
export function solveLinear(rows, rhs, ring, unknownCount) {
  const n = unknownCount ?? (rhs.length ? rows[0].length : 0);
  const m = rows.length;
  const a = rows.map((row, i) => [...row, rhs[i]]);
  const pivots = [];

  let row = 0;
  for (let col = 0; col < n && row < m; col++) {
    let pick = -1;
    for (let r = row; r < m; r++) if (!a[r][col].isZero()) { pick = r; break; }
    if (pick < 0) continue;
    [a[row], a[pick]] = [a[pick], a[row]];
    const inv = ring.one().div(a[row][col]);
    for (let c = col; c <= n; c++) a[row][c] = a[row][c].mul(inv);
    for (let r = 0; r < m; r++) {
      if (r === row || a[r][col].isZero()) continue;
      const factor = a[r][col];
      for (let c = col; c <= n; c++) a[r][c] = a[r][c].sub(factor.mul(a[row][c]));
    }
    pivots.push(col);
    row++;
  }

  for (let r = row; r < m; r++) {
    if (!a[r][n].isZero()) return { status: 'inconsistent' };
  }
  if (pivots.length < n) return { status: 'underdetermined', freedom: n - pivots.length };

  const solution = new Array(n);
  pivots.forEach((col, r) => { solution[col] = a[r][n]; });
  return { status: 'solved', solution };
}

// Смешанный случай: одно квадратичное условие (окружность) плюс линейные.
// Из линейного условия выражаем z̄ через z, подставляем в квадратичное и
// получаем обычное квадратное уравнение — дальше работает тот же механизм, что
// и у пересечения прямой с окружностью: решаем то, что решается без радикалов.
function solveWithQuadratic({ local, symbol, known, unknown, unknownIndices, rows, rhs, quadratic }) {
  if (unknown.length !== 1) {
    throw new Error('условие типа окружности поддержано только для одной неизвестной точки');
  }
  // ДВЕ окружности через одну и ту же неизвестную точку — обычное дело: так
  // ищут вторую точку пересечения двух окружностей, проходящих через общую
  // построенную точку. Отдельного механизма для этого не нужно: разность двух
  // уравнений окружности ЛИНЕЙНА (члены z·z̄ сокращаются) и задаёт радикальную
  // ось. Заменяем одно из условий осью — и дальше работает обычная связка
  // «прямая плюс окружность».
  if (quadratic.length === 2 && rows.length === 0) {
    const axis = radicalAxisRow(quadratic[0], quadratic[1], unknownIndices, local);
    if (axis) {
      rows.push(axis.row);
      rhs.push(axis.rhs);
      quadratic.splice(1, 1);
    }
  }
  if (quadratic.length > 1) {
    throw new Error('двух условий типа окружности сразу движок не решает');
  }
  const reduced = solveLinear(rows, rhs, local, unknownIndices.length);
  if (reduced.status === 'inconsistent') {
    throw new Error('условия противоречат друг другу — решений нет');
  }
  if (reduced.status === 'solved') {
    throw new Error('линейных условий уже достаточно, условие окружности лишнее');
  }
  if (reduced.freedom !== 1 || rows.length === 0) {
    throw new Error(`условий не хватает: осталось ${reduced.freedom ?? 2} `
      + 'степеней свободы, решений бесконечно много');
  }

  // единственная линейная строка: p·z + q·z̄ = r
  const [zIndex, zbarIndex] = unknownIndices;
  const [p, q] = rows[0];
  const r = rhs[0];
  if (q.isZero()) throw new Error('линейное условие не выражает сопряжённую — подставить нечего');

  const values = [];
  for (let v = 0; v < local.size; v++) values[v] = Rational.fromVariable(local, v);
  values[zbarIndex] = r.sub(p.mul(values[zIndex])).div(q);          // z̄ = (r − p z)/q

  const substituted = quadratic[0].substituteInto(values);
  const coeffs = P.coeffsIn(substituted.num, zIndex);
  if (coeffs.length > 3) throw new Error('уравнение выше второй степени — движок такое не решает');
  const at = k => (coeffs[k] ? asLocalRational(local, coeffs[k]) : local.zero());

  const knownValues = known.map(n => symbol.get(n));
  const A = at(2), Bq = at(1), Cq = at(0);
  const solved = solveQuadratic(A, Bq, Cq, knownValues);
  if (solved.roots.length === 0) {
    // КОРЕНЬ ПРИСОЕДИНЯЕМ, А НЕ ИЗВЛЕКАЕМ.
    //
    // Здесь движок раньше капитулировал: «нужны радикалы». Отказ был не по
    // существу, а по недоделке — присоединение корня к полю давно написано
    // (quadratic-ext.js) и работает на пути ПОСТРОЕНИЙ: так мост считает и
    // пересечение прямой с окружностью, и касательные из точки. Решать,
    // извлекается ли корень из многочлена от нескольких переменных, для этого
    // не нужно вовсе — достаточно работать в расширении, где он есть.
    //
    // Присоединить его прямо здесь нельзя: мы в ЛОКАЛЬНОМ кольце, где каждая
    // известная точка — отдельная буква, а настоящие выражения подставляются
    // позже. Расширение, построенное до подстановки, пришлось бы потом
    // переносить в другое кольцо. Поэтому возвращается РЕЦЕПТ: «корень
    // уравнения x² − Sx + Q = 0», где S и Q — обычные элементы локального
    // кольца. Подставив в них вершины, расширение заводит уже вызывающий —
    // ровно так же, как это делает lineMeetsCircleExtended.
    if (A.isZero()) throw new Error('уравнение выродилось: старший коэффициент ноль');
    const S = Bq.div(A).neg();
    const Q = Cq.div(A);
    // Дискриминант вполне может оказаться полным квадратом — тогда корни
    // рациональны, и заводить расширение вредно: все последующие сравнения
    // подорожали бы на ровном месте.
    const root = S.mul(S).sub(Q.mul(4n)).sqrt();
    if (root) {
      const first = S.add(root).div(2n);
      const pair = [first, S.sub(first)];
      const fresh2 = pair.filter(z => !knownValues.some(k => k.equals(z)));
      if (fresh2.length === 1) return { answers: new Map([[unknown[0], fresh2[0]]]) };
      return { pending: { name: unknown[0], S, Q } };
    }
    return { pending: { name: unknown[0], S, Q } };
  }
  // «Берём решения, которые не совпадают с уже нарисованными точками.»
  const fresh = solved.roots.filter(z => !knownValues.some(k => k.equals(z)));
  if (fresh.length === 0) throw new Error('все решения совпадают с уже построенными точками');
  if (fresh.length > 1) throw new Error(`решений несколько (${fresh.length}) — условий не хватает`);
  return { answers: new Map([[unknown[0], fresh[0]]]) };
}

const asLocalRational = (ring, poly) => new Rational(ring, poly, P.constant(ONE));

// ---- решение системы ------------------------------------------------------

// Имена, встречающиеся в аргументах строки. Порядок — порядок появления, чтобы
// буквы в диагностике шли так же, как их написал пользователь.
export function pointNames(commands) {
  const out = [];
  for (const command of commands) {
    for (const ast of command.args) {
      for (const name of namesIn(ast)) if (!out.includes(name)) out.push(name);
    }
  }
  return out;
}

// Решает систему в ЛОКАЛЬНОМ кольце: каждая уже известная точка — просто буква
// со своей независимой сопряжённой. Так исключение Гаусса идёт по нескольким
// переменным вместо всего построения, а раскрытие через a, b, c происходит один
// раз в самом конце.
export function solveSystem(commands, knownNames) {
  const points = pointNames(commands);
  const known = points.filter(p => knownNames.has(p));
  const unknown = points.filter(p => !knownNames.has(p));
  if (unknown.length === 0) throw new Error('в строке нет ни одной новой точки — решать нечего');

  const local = new Ring();
  const symbol = new Map();
  for (const name of known) symbol.set(name, local.freePoint(`«${name}»`));
  for (const name of unknown) symbol.set(name, local.freePoint(`«${name}»`));

  // индексы переменных, по которым решаем: сама точка и её сопряжённая
  const unknownIndices = [];
  const slotOf = new Map();
  for (const name of unknown) {
    const i = local.indexOf(`«${name}»`);
    slotOf.set(name, { z: unknownIndices.length, zbar: unknownIndices.length + 1 });
    unknownIndices.push(i, i + 1);
  }

  const rows = [];
  const rhs = [];
  const quadratic = [];
  const asRational = terms => new Rational(local, P.fromTerms(terms), P.constant(ONE));
  const addEquation = expr => {
    const parts = linearParts(expr.num, unknownIndices);
    if (!parts) { quadratic.push(expr); return; }
    rows.push(unknownIndices.map(v => {
      const terms = parts.coeffs.get(v);
      return terms ? asRational(terms) : local.zero();
    }));
    rhs.push(asRational(parts.constTerms).neg());
  };

  const ctx = { vars: symbol, objects: null, ring: local };
  for (const command of commands) {
    const values = command.args.map(ast => evalAst(ast, ctx));
    const built = command.spec.build(values, command);
    for (const expr of Array.isArray(built) ? built : [built]) {
      addEquation(expr);
      // Комплексное равенство — это два вещественных условия; сопряжённое
      // уравнение независимо и даёт вторую строку. У вещественных условий
      // сопряжённое совпадает с исходным с точностью до знака, второй строки нет.
      if (kindOf(command) === 'complex') addEquation(expr.conjugate());
    }
  }

  // Условие «на одной окружности» содержит член z·z̄ и линейным быть не может —
  // окружность и не задаётся линейным уравнением. Такой случай решается ровно
  // как пересечение прямой с окружностью: выражаем z̄ из линейного условия,
  // подставляем и получаем квадратное уравнение по z.
  if (quadratic.length > 0) {
    const out = solveWithQuadratic({
      local, symbol, known, unknown, unknownIndices, rows, rhs, quadratic,
    });
    // pending — «ответ есть, но он иррационален»: вызывающий подставит вершины
    // в S и Q и заведёт расширение. answers при этом пуст.
    return { local, symbol, known, unknown,
             answers: out.answers ?? new Map(), pending: out.pending ?? null };
  }

  const result = solveLinear(rows, rhs, local);
  if (result.status === 'inconsistent') {
    throw new Error('условия противоречат друг другу — решений нет');
  }
  if (result.status === 'underdetermined') {
    throw new Error(`условий не хватает: осталось ${result.freedom} `
      + `степеней свободы, решений бесконечно много`);
  }

  // Проверка состоятельности: решение для z̄ обязано быть сопряжением решения
  // для z. Если нет — уравнения описывают что-то, чего на плоскости не бывает.
  const answers = new Map();
  for (const name of unknown) {
    const { z, zbar } = slotOf.get(name);
    if (!result.solution[z].conjugate().equals(result.solution[zbar])) {
      throw new Error(`решение для ${name} не согласовано с сопряжением — условия невыполнимы`);
    }
    answers.set(name, result.solution[z]);
  }
  return { local, symbol, known, unknown, answers, pending: null };
}

// ---- условие на точки: не «где точка», а «когда это верно» ----------------
//
// Обратная задача к solveSystem. Там неизвестную ищут, здесь неизвестных нет
// вовсе: все точки строки уже построены, и спрашивается, ПРИ КАКИХ вершинах
// написанное выполняется. Ответ — уравнение на сами образующие: скажем, для
// «медиана из A совпадает с биссектрисой» вылезает множитель (b − c), то есть
// равнобедренность.
//
// Считать надо в ГЛАВНОМ кольце, а не в локальном, как solveSystem. Там локальное
// кольцо — оптимизация: неизвестную исключают среди нескольких букв, а раскрытие
// через a, b, c откладывают на потом. Здесь раскрытие и есть ответ, откладывать
// нечего, и лишний слой только мешал бы.
//
// Каждое условие даёт «выражение = 0». Знаменатель отбрасываем: дробь равна
// нулю тогда и только тогда, когда числитель равен нулю (знаменатель не может
// обратиться в ноль — там стоят разности различных точек). Печать сама разложит
// числитель на множители, а разложение здесь и есть содержательный ответ:
// каждый множитель — отдельный вырожденный случай.
export function conditionEquations(commands, values) {
  const builds = commands.filter(c => kindOf(c) === 'build');
  if (builds.length > 0) {
    throw new Error(`${builds[0].name} — это построение, а не условие; здесь нужны условия`);
  }

  const names = pointNames(commands);
  const missing = names.filter(n => !values.has(n));
  if (missing.length > 0) {
    throw new Error(`точк${missing.length > 1 ? 'и' : 'а'} ${missing.join(', ')} `
      + `не построен${missing.length > 1 ? 'ы' : 'а'}: условие можно писать только на то, что уже есть`);
  }
  if (names.length === 0) throw new Error('в условии нет ни одной точки');

  // Кольцо берём БАЗОВОЕ. Если первая точка иррациональна, её `ring` — это
  // расширение, а уравнение обязано быть записано в буквах вершин.
  const ring = baseRingOf(values.get(names[0]).ring);
  const ctx = { vars: values, objects: null, ring: values.get(names[0]).ring };

  const out = [];
  for (const command of commands) {
    const args = command.args.map(ast => evalAst(ast, ctx));
    const built = command.spec.build(args, command);
    for (const expr of Array.isArray(built) ? built : [built]) {
      const value = descendToBase(expr);
      const equation = new Rational(ring, value.num, P.constant(ONE));
      out.push({
        command,
        // Числитель как самостоятельная величина — его и печатаем «… = 0».
        equation,
        // Тождественный ноль означает, что условие выполняется всегда: это не
        // уравнение на треугольник, а верное для любого утверждение.
        identity: value.num.isZero(),
        // Обратный полюс: НЕНУЛЕВАЯ константа. «512 = 0» формально верно, но
        // читается как задача, у которой надо найти решение, — а решений нет
        // ни при каком треугольнике. Отдельная пометка честнее.
        //
        // Раньше такие константы были редкостью, а со спуском по норме стали
        // обычным делом: норма домножает уравнение на сопряжённое, и там, где
        // выходило «1 = 0», теперь выходит «512 = 0».
        impossible: !value.num.isZero() && P.terms(value.num).every(t => t.exp.every(e => e === 0)),
      });
    }
  }
  return out;
}

// Спуск с башни расширений: превращает условие, записанное через корни, в
// условие на сами вершины.
//
// Зачем. Значение из расширения — это пара `a + b·x`, и «условие выполнено»
// значит `a + b·x = 0`. В базисе {1, x} это ДВА условия сразу (a = 0 и b = 0),
// а печатать надо ОДНО, и притом уравнение на буквы вершин: ответ вида
// «выполняется, когда ... = 0» с иррациональным корнем внутри ничего не
// объясняет и на множители не раскладывается.
//
// Норма делает ровно это. N(a + b·x) = (a + b·x)(a + b·y) = a² + abS + b²Q
// лежит ЭТАЖОМ НИЖЕ и обращается в ноль ровно тогда, когда a = b = 0:
//
//   * если a = b = 0, то и норма ноль — очевидно;
//   * обратно, пусть N = 0 и b ≠ 0. Тогда x = −a/b лежал бы в базовом поле, а
//     расширение заводится только на НЕРАЗЛОЖИМОМ уравнении (дискриминант
//     проверяется на точный квадрат до присоединения) — противоречие. Значит
//     b = 0, и тогда N = a², откуда a = 0.
//
// Так что замена условия его нормой ничего не теряет и ничего не добавляет —
// множество решений то же самое. Спускаемся по всей башне, пока не окажемся в
// обычном поле рациональных функций.
function descendToBase(value) {
  let v = value;
  while (v?.isAlg) v = v.norm();
  return v;
}

// Радикальная ось двух условий «на одной окружности».
//
// Условие cocycl содержит член z·z̄ и линейным быть не может — окружность
// линейным уравнением не задаётся. Но РАЗНОСТЬ двух таких условий линейна:
// достаточно уравнять коэффициенты при z·z̄, и они сократятся. Геометрически
// это и есть радикальная ось двух окружностей, а на ней лежит их пересечение.
//
// null, если сократить не вышло: тогда вызывающий честно скажет, что двух
// условий окружности сразу не решает.
function radicalAxisRow(first, second, unknownIndices, local) {
  const [zIndex, zbarIndex] = unknownIndices;

  const mixedCoeff = poly => {
    const byZ = P.coeffsIn(poly, zIndex);
    if (byZ.length < 2) return null;
    const byZbar = P.coeffsIn(byZ[1], zbarIndex);
    return byZbar.length < 2 || byZbar[1].isZero() ? null : byZbar[1];
  };

  const n1 = first.num, n2 = second.num;
  const c1 = mixedCoeff(n1), c2 = mixedCoeff(n2);
  if (!c1 || !c2) return null;

  const combined = P.sub(P.mul(n1, c2), P.mul(n2, c1));
  const parts = linearParts(combined, unknownIndices);
  if (!parts) return null;

  const asRational = terms => new Rational(local, P.fromTerms(terms), P.constant(ONE));
  return {
    row: unknownIndices.map(v => {
      const terms = parts.coeffs.get(v);
      return terms ? asRational(terms) : local.zero();
    }),
    rhs: asRational(parts.constTerms).neg(),
  };
}
