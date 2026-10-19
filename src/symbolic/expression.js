import { rootOfUnity } from './unity.js';
// Пользовательские выражения: P - Q, (X-Y)/(X-Z), с переменными.
//
// Разбор и вычисление здесь РАЗДЕЛЕНЫ. Раньше парсер сразу складывал Rational
// по ходу чтения, и это было проще, — но выражения понадобились ещё и в
// аргументах команд (perpen(A, P, Q+A/3, …)), а там во время разбора кольца
// ещё нет: неизвестные точки становятся образующими локального кольца уже
// после того, как выяснилось, какие имена в строке встречаются. Поэтому
// parseExpression отдаёт дерево, namesIn собирает по нему имена, и только
// потом evalAst считает — в том кольце, в каком нужно.
//
// Ответ просто раскладывается на множители. Автоматической проверки на
// вещественность здесь НЕТ: она требует сопряжения всего выражения и нескольких
// сравнений, то есть стоит дороже самого вычисления, а нужна далеко не всегда.
// Кому нужна — пишет её явно: «X - conj(X)» обнулится ровно тогда, когда X
// вещественно, а ноль виден сразу и бесплатно.

const OPERATORS = new Set(['+', '-', '*', '/', '^']);

function tokenize(source) {
  const tokens = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i];
    if (/\s/.test(ch)) { i++; continue; }
    // Степень пишется и как ^, и как ** — второе привычнее тем, кто пишет на
    // Python, а спутать её здесь не с чем.
    if (ch === '*' && source[i + 1] === '*') {
      tokens.push({ kind: 'op', text: '^', at: i });
      i += 2;
      continue;
    }
    if (OPERATORS.has(ch) || ch === '(' || ch === ')' || ch === ',' || ch === '=') {
      const kind = ch === '=' ? '=' : (ch === '(' || ch === ')' || ch === ',' ? ch : 'op');
      tokens.push({ kind, text: ch, at: i });
      i++;
      continue;
    }
    if (/[0-9]/.test(ch)) {
      let j = i;
      while (j < source.length && /[0-9]/.test(source[j])) j++;
      tokens.push({ kind: 'number', text: source.slice(i, j), at: i });
      i = j;
      continue;
    }
    if (/[A-Za-zА-Яа-я_]/.test(ch)) {
      let j = i;
      while (j < source.length && /[A-Za-zА-Яа-я0-9_']/.test(source[j])) j++;
      tokens.push({ kind: 'name', text: source.slice(i, j), at: i });
      i = j;
      continue;
    }
    throw new Error(`непонятный символ «${ch}» в позиции ${i + 1}`);
  }
  return tokens;
}

// ---- функции --------------------------------------------------------------
//
// conj нужен постоянно: почти любая проверка в комплексной планиметрии сводится
// к сравнению выражения с его сопряжением.
//
// distance берёт аргументы НЕРАЗОБРАННЫМИ (raw): её аргументом бывает не точка,
// а имя прямой или окружности с панели, и отличить одно от другого можно только
// по самому имени, до вычисления.
const FUNCTIONS = {
  conj: { arity: 1, apply: ([x]) => x.conjugate() },
  сопр: { arity: 1, apply: ([x]) => x.conjugate() },
  distance: { arity: 2, raw: true, apply: (nodes, ctx) => squaredDistance(nodes, ctx) },
  расст: { arity: 2, raw: true, apply: (nodes, ctx) => squaredDistance(nodes, ctx) },
  unity: { arity: 1, raw: true, apply: (nodes, ctx) => unityOf(nodes, ctx) },
};
FUNCTIONS['корень'] = FUNCTIONS.unity;

export const FUNCTION_NAMES = new Set(Object.keys(FUNCTIONS));

// unity(n) — первообразный корень степени n из единицы, то есть направление
// поворота на 360°/n. Аргумент берётся НЕРАЗОБРАННЫМ и обязан быть числом:
// степень корня — это про то, какое поле мы строим, а не величина в нём, и
// unity(a) смысла не имеет.
//
// Отсюда поворот на понятный угол пишется одной строкой без всякой особой
// команды: buildpoint(C + (P − C)*unity(6)) — это поворот P вокруг C на 60°.
function unityOf(nodes, ctx) {
  const node = nodes[0];
  const n = node.t === 'num' ? Number(node.value)
    : (node.t === 'neg' && node.arg.t === 'num' ? -Number(node.arg.value) : null);
  if (n === null) {
    throw new Error('unity: степень корня должна быть числом, записанным прямо в скобках');
  }
  return rootOfUnity(ctx.ring, n);
}

// Квадрат расстояния. Именно квадрат: сам корень иррационален и вывел бы
// выражение за пределы поля, в котором работает движок, а во всех проверках
// («равные отрезки», «степень точки») он и так стоит в квадрате.
function squaredDistance(nodes, ctx) {
  const resolve = node => {
    if (node.t === 'name') {
      const obj = ctx.objects?.get(node.name);
      if (obj) return obj;
    }
    return { kind: 'point', value: evalAst(node, ctx) };
  };
  const [x, y] = nodes.map(resolve);

  if (x.kind === 'point' && y.kind === 'point') {
    const d = x.value.sub(y.value);
    return d.mul(d.conjugate());
  }
  const [p, other] = x.kind === 'point' ? [x, y] : [y, x];
  if (p.kind !== 'point') {
    throw new Error('distance: хотя бы один из двух объектов должен быть точкой');
  }
  if (other.kind === 'line') {
    // Отражение точки в прямой удалено от неё вдвое дальше самой прямой,
    // поэтому квадрат расстояния — четверть квадрата длины отрезка до образа.
    const d = p.value.sub(other.eq.reflect(p.value));
    return d.mul(d.conjugate()).div(4n);
  }
  // До окружности считается СТЕПЕНЬ ТОЧКИ: точка просто подставляется в
  // уравнение. Расстояние до самой окружности потребовало бы корня.
  return other.eq.residual(p.value);
}

// ---- разбор ---------------------------------------------------------------

class Parser {
  // Набор функций передаётся снаружи: у Бариканатора он свой (line, det, abs,
  // EFFT), а разбор — тот же самый. Без этого пришлось бы держать второй
  // экземпляр парсера ради одной строчки в parsePrimary.
  constructor(tokens, functions = FUNCTIONS) {
    this.tokens = tokens;
    this.pos = 0;
    this.functions = functions;
  }

  peek() { return this.tokens[this.pos]; }
  next() { return this.tokens[this.pos++]; }
  eatOp(...texts) {
    const t = this.peek();
    if (t && t.kind === 'op' && texts.includes(t.text)) { this.pos++; return t.text; }
    return null;
  }

  parseExpression() {
    let left = this.parseTerm();
    for (;;) {
      const op = this.eatOp('+', '-');
      if (!op) return left;
      left = { t: op === '+' ? 'add' : 'sub', left, right: this.parseTerm() };
    }
  }

  parseTerm() {
    let left = this.parsePower();
    for (;;) {
      const op = this.eatOp('*', '/');
      if (!op) return left;
      left = { t: op === '*' ? 'mul' : 'div', left, right: this.parsePower() };
    }
  }

  parsePower() {
    const base = this.parseUnary();
    if (!this.eatOp('^')) return base;
    const t = this.peek();
    let sign = 1;
    if (t && t.kind === 'op' && (t.text === '-' || t.text === '+')) {
      sign = this.next().text === '-' ? -1 : 1;
    }
    const exp = this.next();
    if (!exp || exp.kind !== 'number') throw new Error('после ^ ожидается целая степень');
    const power = Number(exp.text) * sign;
    if (!Number.isSafeInteger(power) || Math.abs(power) > 32) {
      throw new Error(`степень ${power} слишком велика`);
    }
    return { t: 'pow', base, power };
  }

  parseUnary() {
    const op = this.eatOp('-', '+');
    if (op === '-') return { t: 'neg', arg: this.parseUnary() };
    if (op === '+') return this.parseUnary();
    return this.parsePrimary();
  }

  parsePrimary() {
    const t = this.next();
    if (!t) throw new Error('выражение оборвалось');
    if (t.kind === '(') {
      const inner = this.parseExpression();
      const close = this.next();
      if (!close || close.kind !== ')') throw new Error('не закрыта скобка');
      return inner;
    }
    if (t.kind === 'number') return { t: 'num', value: BigInt(t.text) };
    if (t.kind === 'name') {
      const spec = this.functions[t.text.toLowerCase()];
      if (spec) return this.parseCall(t.text, spec);
      return { t: 'name', name: t.text };
    }
    throw new Error(`здесь не ждали «${t.text}»`);
  }

  parseCall(name, spec) {
    const open = this.next();
    if (!open || open.kind !== '(') throw new Error(`после ${name} ожидается скобка`);
    const args = [this.parseExpression()];
    while (this.peek()?.kind === ',') {
      this.next();
      args.push(this.parseExpression());
    }
    const close = this.next();
    if (!close || close.kind !== ')') throw new Error('не закрыта скобка');
    if (args.length !== spec.arity) {
      throw new Error(`${name}: ожидалось аргументов — ${spec.arity}, получено ${args.length}`);
    }
    return { t: 'call', name: name.toLowerCase(), args };
  }
}

export function parseExpression(source, functions = FUNCTIONS) {
  const tokens = tokenize(source);
  if (tokens.length === 0) throw new Error('пустое выражение');
  if (tokens.some(x => x.kind === '=')) throw new Error('знак = здесь не к месту');
  const parser = new Parser(tokens, functions);
  const ast = parser.parseExpression();
  if (parser.pos < tokens.length) {
    throw new Error(`лишнее после выражения: «${tokens[parser.pos].text}»`);
  }
  return ast;
}

// Все имена, встречающиеся в дереве как значения. Имена функций сюда не
// попадают — по ним и отличаются вызовы от точек.
export function namesIn(ast, out = new Set()) {
  switch (ast.t) {
    case 'name': out.add(ast.name); break;
    case 'neg': namesIn(ast.arg, out); break;
    case 'pow': namesIn(ast.base, out); break;
    case 'call': for (const a of ast.args) namesIn(a, out); break;
    case 'add': case 'sub': case 'mul': case 'div':
      namesIn(ast.left, out); namesIn(ast.right, out); break;
    default: break;
  }
  return out;
}

// ---- вычисление -----------------------------------------------------------

// ctx: { vars: Map<имя, Rational>, objects?: Map<имя, {kind, eq}>, ring }
export function evalAst(ast, ctx) {
  switch (ast.t) {
    case 'num': return ctx.ring.constant(ast.value);
    case 'name': {
      const value = ctx.vars.get(ast.name);
      if (value) return value;
      const obj = ctx.objects?.get(ast.name);
      if (obj) {
        const what = obj.kind === 'line' ? 'прямая' : 'окружность';
        throw new Error(`«${ast.name}» — это ${what}, а здесь нужна точка`);
      }
      throw new Error(`не знаю, что такое «${ast.name}»`);
    }
    case 'neg': return evalAst(ast.arg, ctx).neg();
    case 'add': return evalAst(ast.left, ctx).add(evalAst(ast.right, ctx));
    case 'sub': return evalAst(ast.left, ctx).sub(evalAst(ast.right, ctx));
    case 'mul': return evalAst(ast.left, ctx).mul(evalAst(ast.right, ctx));
    case 'div': {
      const right = evalAst(ast.right, ctx);
      if (right.isZero()) throw new Error('деление на ноль');
      return evalAst(ast.left, ctx).div(right);
    }
    case 'pow': {
      const base = evalAst(ast.base, ctx);
      if (ast.power < 0 && base.isZero()) throw new Error('деление на ноль');
      const factor = ast.power < 0 ? ctx.ring.one().div(base) : base;
      let acc = ctx.ring.one();
      for (let k = 0; k < Math.abs(ast.power); k++) acc = acc.mul(factor);
      return acc;
    }
    case 'call': {
      const spec = FUNCTIONS[ast.name];
      if (!spec) throw new Error(`неизвестная функция «${ast.name}»`);
      if (spec.raw) return spec.apply(ast.args, ctx);
      return spec.apply(ast.args.map(a => evalAst(a, ctx)), ctx);
    }
    default: throw new Error(`непонятный узел ${ast.t}`);
  }
}

// Имя переменной длиной в одну букву слишком легко спутать с точкой чертежа
// (A, B, C) и с образующими (a, b, c), поэтому требуем хотя бы две.
export const VARIABLE_NAME = /^[A-Za-zА-Яа-я_][A-Za-zА-Яа-я0-9_']+$/;

// Разбор строки вида «имя = выражение». Само вычисление у каждого движка своё,
// а вот проверка имени переменной и запрет второго знака = — общие.
export function parseAssignment(source, functions = FUNCTIONS) {
  const tokens = tokenize(source);
  if (tokens.length === 0) return null;
  let target = null;
  let body = tokens;
  if (tokens.length > 2 && tokens[0].kind === 'name' && tokens[1].kind === '=') {
    target = tokens[0].text;
    if (functions[target.toLowerCase()]) throw new Error(`«${target}» — это функция, не имя переменной`);
    if (!VARIABLE_NAME.test(target)) {
      throw new Error(`имя «${target}» короче двух знаков — так его не отличить от точки чертежа`);
    }
    body = tokens.slice(2);
    if (body.some(t => t.kind === '=')) {
      throw new Error('знак = допустим только один раз, как присваивание в начале строки');
    }
  } else if (tokens.some(t => t.kind === '=')) {
    throw new Error('знак = допустим только как присваивание в начале строки');
  }
  const parser = new Parser(body, functions);
  const ast = parser.parseExpression();
  if (parser.pos < body.length) {
    throw new Error(`лишнее после выражения: «${body[parser.pos].text}»`);
  }
  return { target, ast };
}

export function evaluateLine(source, env, ring, objects = null) {
  const tokens = tokenize(source);
  if (tokens.length === 0) return null;

  let target = null;
  let body = tokens;
  // присваивание: имя = выражение
  if (tokens.length > 2 && tokens[0].kind === 'name' && tokens[1].kind === '=') {
    target = tokens[0].text;
    if (FUNCTIONS[target.toLowerCase()]) throw new Error(`«${target}» — это функция, не имя переменной`);
    if (!VARIABLE_NAME.test(target)) {
      throw new Error(`имя «${target}» короче двух знаков — так его не отличить от точки чертежа`);
    }
    body = tokens.slice(2);
    if (body.some(t => t.kind === '=')) {
      throw new Error('знак = допустим только один раз, как присваивание в начале строки');
    }
  } else if (tokens.some(t => t.kind === '=')) {
    throw new Error('знак = допустим только как присваивание в начале строки');
  }

  const parser = new Parser(body);
  const ast = parser.parseExpression();
  if (parser.pos < body.length) {
    throw new Error(`лишнее после выражения: «${body[parser.pos].text}»`);
  }
  const value = evalAst(ast, { vars: env, objects, ring });
  // Единственная приписка, которая ничего не стоит: числитель уже посчитан.
  return { target, value, nature: value.isZero() ? 'ноль' : null };
}
