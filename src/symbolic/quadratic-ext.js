import { Rational } from './rational.js';
import { CFrac } from './complex-fraction.js';
import { sqrtCFrac } from './gcd.js';

// Квадратичное расширение поля рациональных функций.
//
// Задача: пересечение прямой с окружностью (или двух окружностей) сплошь и рядом
// даёт два корня, ни один из которых не выражается через a, b, c. По отдельности
// они иррациональны — но связаны теоремой Виета, и почти всё, что из них потом
// строится, от выбора «который из двух» не зависит.
//
// НАПРАШИВАЮЩЕЕСЯ решение — завести две буквы x, y, помнить x+y = S и x·y = Q и
// вычёркивать симметрические части по мере появления — плохо тем, что это не
// нормальная форма, а переписывание. Для x+y и x·y правило очевидно, а вот x²y —
// это (xy)·x = Q·x, наполовину симметрично; нужна система переписывания и
// доказательство её конфлюэнтности. Движку же нормальная форма нужна на каждом
// шагу: equals, isZero, contains — это каждое сравнение прямых и каждая проверка
// принадлежности.
//
// Здесь сделано иначе: y исключается сразу как y = S − x, после чего x
// удовлетворяет
//
//     x² = S·x − Q
//
// и КАЖДЫЙ элемент однозначно записывается как a + b·x с a, b из базового поля.
// Это не эвристика, а обычная теорема: R[x,y]/(x+y−S, xy−Q) — свободный модуль
// ранга 2 над R с базисом {1, x}. Отсюда всё остальное:
//
//   * форма единственна, поэтому сравнение — это сравнение двух пар, а isZero
//     ничего не стоит;
//   * симметрические части схлопываются САМИ: x+y даёт S, x·y даёт Q — не по
//     правилу, а как следствие приведения;
//   * деление честное: (a+bx)⁻¹ = (a+by)/N, где N = a² + abS + b²Q — норма, уже
//     обычная рациональная функция;
//   * размер жёстко ограничен: ровно два элемента базового поля на значение.
//
// Асимметрия при этом никуда не девается и деваться не должна: x − y = 2x − S,
// и это действительно иррациональная величина.
//
// Интерфейс намеренно повторяет Rational (add/sub/mul/div/conjugate/isZero/
// equals, а у «кольца» — one/zero/constant/i). Благодаря этому вся геометрия —
// LineEq, CircleEq, formulas — работает с расширением без единой правки: она
// написана обобщённо и про природу коэффициентов ничего не знает.

let extCounter = 0;

// Самое нижнее кольцо башни — то, в котором живут буквы вершин. Нужно всюду,
// где ответ обязан быть записан через a, b, c, а на входе может оказаться
// значение любого этажа.
export function baseRingOf(ring) {
  let r = ring;
  while (r instanceof QuadraticExt) r = r.base;
  return r;
}

export class QuadraticExt {
  // S = x + y, Q = x·y — коэффициенты по Виету, оба из базового кольца.
  constructor(base, S, Q, name = 'x') {
    this.base = base;
    // Номер создания: по нему объединение независимых расширений выбирает, какое
    // из них станет основанием. Без такого порядка «x над y» и «y над x» дали бы
    // разные поля, и значения, полученные в разном порядке, не сравнились бы.
    this.id = ++extCounter;
    this.S = S;
    this.Q = Q;
    this.name = name;
    // conj(x) как элемент этого же расширения. Задаётся отдельно, потому что
    // зависит от того, ЧЕМ является x: у точки на окружности своё правило.
    this.conjRoot = null;
  }

  // Правило сопряжения для точки, лежащей на окружности (o, r²):
  // conj(x) = ō + r²/(x − o). Оно же годится и для второго корня: оба корня
  // лежат на этой окружности, а правило зависит только от самой точки.
  setCircleRule(circle) {
    const o = this.lift(circle.center);
    const shifted = this.root().sub(o);
    this.conjRoot = this.lift(circle.center.conjugate())
      .add(this.lift(circle.r2).div(shifted));
    return this;
  }

  // Базой может быть как обычное кольцо, так и ДРУГОЕ расширение — тогда
  // получается башня. Никакого особого случая для этого не нужно: значение
  // нижнего уровня просто кладётся в коэффициент при 1.
  // Как перенести в это поле значение из поля `from`, если это вообще возможно.
  //
  // Три случая, и все три обязаны разбираться ОДНИМ механизмом — иначе, как уже
  // случалось, значение оказывается «чужим» там, где на самом деле оно своё, и
  // движок заводит третье поле вместо того, чтобы посчитать:
  //   * это же поле — ничего делать не надо;
  //   * поле ниже по башне — обернуть, рекурсивно;
  //   * поле, вложенное сюда при объединении независимых расширений, — перенести
  //     его собственным правилом (см. joinExtensions).
  carrierFor(from) {
    if (from === this) return v => v;
    const embedded = this.embeddings?.get(from);
    if (embedded) return embedded;
    if (this.base instanceof QuadraticExt) {
      const inner = this.base.carrierFor(from);
      if (inner) return v => new Alg(this, inner(v), this.base.zero());
    }
    return null;
  }

  lift(value) {
    if (value instanceof Alg) {
      const carry = this.carrierFor(value.ext);
      if (carry) return carry(value);
      throw new Error('Alg: значения из разных расширений');
    }
    if (value instanceof Rational) return new Alg(this, value, this.base.zero());
    return new Alg(this, this.base.constant(value), this.base.zero());
  }

  zero() { return new Alg(this, this.base.zero(), this.base.zero()); }
  one() { return new Alg(this, this.base.one(), this.base.zero()); }
  i() { return new Alg(this, this.base.i(), this.base.zero()); }
  constant(v) { return this.lift(v); }

  // Сам присоединённый корень и второй корень того же уравнения.
  root() { return new Alg(this, this.base.zero(), this.base.one()); }
  other() { return new Alg(this, this.S, this.base.constant(-1n)); }
}

// Два НЕЗАВИСИМЫХ расширения над одной базой — обычное дело для построений
// циркулем и линейкой: два разных пересечения дают два разных корня, а потом
// через обе точки проводят прямую.
//
// Складывать их напрямую нельзя: это элементы разных полей. Но объединить их
// можно всегда — надстроив второе НАД первым. Уравнение второго корня живёт в
// базе, база вкладывается в первое расширение, значит там же живёт и уравнение;
// присоединяем его — и получаем поле, где лежат оба корня. Независимость так
// превращается во вложенность, а вложенность у нас уже работает.
//
// Объединение кэшируется: без этого два одинаковых по смыслу значения оказались
// бы в разных (хоть и одинаково устроенных) полях и никогда бы не сравнились.
// Все этажи башни снизу вверх (само кольцо в список не входит).
function levelsOf(ext) {
  const out = [];
  for (let e = ext; e instanceof QuadraticExt; e = e.base) out.unshift(e);
  return out;
}

// Поле определяется НАБОРОМ присоединённых корней, а не порядком, в котором их
// присоединяли. Ключ — отсортированные номера уровней: тогда одно и то же поле
// получается независимо от того, с какой стороны к нему пришли, и значения из
// разных веток вычисления сравниваются между собой.
const joinCache = new Map();

function joinExtensions(x, y) {
  const byId = new Map();
  for (const level of [...levelsOf(x), ...levelsOf(y)]) {
    if (!byId.has(level.id)) byId.set(level.id, level);
  }
  const ids = [...byId.keys()].sort((p, q) => p - q);
  const key = ids.join(',');
  const cached = joinCache.get(key);
  if (cached) return cached;

  // Надстраиваем этажи по очереди. Порядок по номеру создания не случаен:
  // уравнение каждого этажа живёт в его базе, а база всегда создана раньше —
  // значит к моменту надстройки она уже вмещается в собираемое поле.
  let ext = null;
  for (const id of ids) {
    const level = byId.get(id);
    if (ext === null) { ext = level; continue; }   // нижний этаж берём как есть
    if (ext.carrierFor(level)) continue;           // этот корень уже внутри

    // Уравнение, неприводимое над своей базой, может стать РАЗЛОЖИМЫМ над
    // накопленным полем — и тогда присоединять нечего, корень уже здесь.
    //
    // Это не тонкость, а суть дела. Середины дуг связаны: u² = bc, v² = ca,
    // w² = ab, откуда uv = ±c·w. Присоединив u и v, мы уже получили w — а
    // движок, не заметив этого, строил поле вдвое больше настоящего. В таком
    // поле корни алгебраически свободны, и тождества, которые держатся именно
    // на связи между ними (три биссектрисы сходятся в инцентре), перестают
    // выполняться. Формулы при этом верные, а проверки — ложно отрицательные.
    const S = ext.lift(level.S);
    const Q = ext.lift(level.Q);
    const inside = S.mul(S).sub(Q.mul(4n)).sqrt?.();
    if (inside) {
      const value = S.add(inside).div(2n);
      if (!ext.embeddings) ext.embeddings = new Map();
      ext.embeddings.set(level, v => ext.lift(v.a).add(ext.lift(v.b).mul(value)));
      continue;
    }

    const next = new QuadraticExt(ext, S, Q, level.name);
    // Вложение: значение старого этажа a + b·x переносится в новый как есть,
    // потому что корень у них один и тот же. Без этой записи старый этаж
    // остался бы «чужим», и на нём завелось бы ещё одно поле вместо счёта.
    next.embeddings = new Map([[level,
      v => next.lift(v.a).add(next.lift(v.b).mul(next.root()))]]);
    if (level.conjRoot) next.conjRoot = next.embeddings.get(level)(level.conjRoot);
    // Корень тот же, значит и точка на чертеже, и её численное значение — тоже.
    next.ggbRoot = level.ggbRoot;
    next.ggbName = level.ggbName;
    next.numericRoot = level.numericRoot;
    ext = next;
  }

  const join = { ext };
  joinCache.set(key, join);
  return join;
}

// Численное значение присоединённого корня.
//
// Для живой сверки с чертежом оно берётся С ЧЕРТЕЖА (ext.numericRoot): корень
// ЕСТЬ точка, построенная GeoGebra, и это надёжнее радикала — никакого выбора
// ветви. Но генератор считает не на нарисованном треугольнике, а на СЛУЧАЙНОМ,
// и там значение с чертежа не имеет отношения к делу: точка пересечения уехала
// вместе с вершинами. Подставляя старое, мы получали для таких точек
// координаты чужой конфигурации — молча, без всякой ошибки, и любые факты о
// них становились случайными.
//
// Поэтому когда инстанциация приносит с собой таблицу корней (values.roots),
// корень считается по Виету прямо здесь: x = (S + √(S²−4Q))/2. Какую из двух
// ветвей даст √, неважно — важно, что в пределах одной инстанциации она одна и
// та же для всех значений над этим расширением. Факт, верный символьно, верен
// для ОБОИХ корней (проверка использует лишь x² = Sx − Q), так что выбор ветви
// не может ни потерять теорему, ни выдумать её.
function rootFloat(ext, values) {
  const cache = values?.roots;
  if (!cache) return ext.numericRoot;
  const hit = cache.get(ext);
  if (hit) return hit;
  const S = ext.S.evalFloat(values), Q = ext.Q.evalFloat(values);
  const disc = { re: S.re * S.re - S.im * S.im - 4 * Q.re, im: 2 * S.re * S.im - 4 * Q.im };
  const m = Math.sqrt(Math.hypot(disc.re, disc.im));
  const th = Math.atan2(disc.im, disc.re) / 2;
  const root = { re: (S.re + m * Math.cos(th)) / 2, im: (S.im + m * Math.sin(th)) / 2 };
  cache.set(ext, root);
  return root;
}

export class Alg {
  // a + b·x
  constructor(ext, a, b) {
    this.ext = ext;
    // Метка для Rational: по ней смешанные операции уходят сюда, и это дешевле
    // кольцевого импорта.
    this.isAlg = true;
    this.a = a;
    this.b = b;
  }

  get ring() { return this.ext; }

  lift(v) { return this.ext.lift(v); }

  // Значение с уровня ВЫШЕ по башне: наш уровень в него вложен, поэтому
  // операцию должен выполнять он, а не мы. Без этого прямая, коэффициенты
  // которой живут на первом этаже, не умеет проверить принадлежность точки,
  // найденной на втором, — а это ровно то, зачем башня и нужна.
  #higher(o) {
    if (!o?.isAlg || o.ext === this.ext) return null;
    if (this.ext.carrierFor(o.ext)) return null;      // справлюсь сам
    return o.ext.carrierFor(this.ext) ? o : null;     // а вот он меня вмещает
  }

  // Значение из НЕЗАВИСИМОГО расширения: ни оно не вмещает меня, ни я его.
  // Такие приводятся к общему полю (см. joinExtensions).
  #alien(o) {
    if (!o?.isAlg || o.ext === this.ext) return null;
    if (this.ext.carrierFor(o.ext) || o.ext.carrierFor(this.ext)) return null;
    return o;
  }

  // Приводит оба значения к общему полю и выполняет там операцию.
  #together(o, op) {
    // Общее поле вмещает оба значения по построению, поэтому переносить их
    // отдельными путями не нужно: lift сам находит дорогу через carrierFor.
    const { ext } = joinExtensions(this.ext, o.ext);
    return op(ext.lift(this), ext.lift(o));
  }

  #unusedToJoin(o) {
    const { ext } = joinExtensions(this.ext, o.ext);
    return ext.lift(this);
  }

  add(o) {
    const alien = this.#alien(o);
    if (alien) return this.#together(alien, (x, y) => x.add(y));
    const up = this.#higher(o);
    if (up) return up.add(this);
    o = this.lift(o);
    return new Alg(this.ext, this.a.add(o.a), this.b.add(o.b));
  }

  sub(o) {
    const alien = this.#alien(o);
    if (alien) return this.#together(alien, (x, y) => x.sub(y));
    const up = this.#higher(o);
    if (up) return up.neg().add(this);
    o = this.lift(o);
    return new Alg(this.ext, this.a.sub(o.a), this.b.sub(o.b));
  }

  neg() { return new Alg(this.ext, this.a.neg(), this.b.neg()); }

  // (a₁+b₁x)(a₂+b₂x) = a₁a₂ + (a₁b₂+a₂b₁)x + b₁b₂x², и x² = Sx − Q.
  mul(o) {
    const alien = this.#alien(o);
    if (alien) return this.#together(alien, (x, y) => x.mul(y));
    const up = this.#higher(o);
    if (up) return up.mul(this);
    o = this.lift(o);
    const { S, Q } = this.ext;
    const bb = this.b.mul(o.b);
    return new Alg(
      this.ext,
      this.a.mul(o.a).sub(bb.mul(Q)),
      this.a.mul(o.b).add(o.a.mul(this.b)).add(bb.mul(S)),
    );
  }

  // Сопряжение ПО РАСШИРЕНИЮ (x ↔ y), не комплексное: a + bx ↦ a + by.
  // Это то, чем домножают при делении.
  swapRoots() {
    return new Alg(this.ext, this.a.add(this.b.mul(this.ext.S)), this.b.neg());
  }

  // Норма N(a+bx) = (a+bx)(a+by) = a² + abS + b²Q — уже элемент базового поля.
  // Ноль она даёт только на нуле: у неприводимого уравнения корней в базовом
  // поле нет, поэтому делитель нуля тут появиться не может.
  norm() {
    const { S, Q } = this.ext;
    return this.a.mul(this.a)
      .add(this.a.mul(this.b).mul(S))
      .add(this.b.mul(this.b).mul(Q));
  }

  inv() {
    const n = this.norm();
    if (n.isZero()) throw new Error('Alg: деление на ноль');
    const swapped = this.swapRoots();
    return new Alg(this.ext, swapped.a.div(n), swapped.b.div(n));
  }

  div(o) {
    const alien = this.#alien(o);
    if (alien) return this.#together(alien, (x, y) => x.div(y));
    const up = this.#higher(o);
    if (up) return up.inv().mul(this);
    o = this.lift(o);
    // Деление на элемент базового поля не требует ни нормы, ни обращения.
    if (o.b.isZero()) {
      if (o.a.isZero()) throw new Error('Alg: деление на ноль');
      return new Alg(this.ext, this.a.div(o.a), this.b.div(o.a));
    }
    return this.mul(o.inv());
  }

  // Комплексное сопряжение: структурное, как и везде в движке. Сопрягаем
  // коэффициенты и подставляем правило для самого корня.
  conjugate() {
    if (!this.ext.conjRoot) {
      throw new Error('Alg: для присоединённого корня не задано правило сопряжения');
    }
    return this.ext.lift(this.a.conjugate())
      .add(this.ext.lift(this.b.conjugate()).mul(this.ext.conjRoot));
  }

  isZero() { return this.a.isZero() && this.b.isZero(); }
  equals(o) {
    const alien = this.#alien(o);
    if (alien) return this.#together(alien, (x, y) => x.equals(y));
    const up = this.#higher(o);
    if (up) return up.equals(this);
    o = this.lift(o);
    return this.a.equals(o.a) && this.b.equals(o.b);
  }

  // Точный квадратный корень внутри расширения. Нужен, чтобы строить БАШНЮ:
  // на втором уровне проверка «а не разложимо ли уравнение» спрашивает корень
  // из дискриминанта, который сам уже лежит в первом расширении. Без этой
  // проверки можно построить «расширение» по разложимому многочлену — а это
  // уже не поле: норма ненулевого элемента обращается в ноль, и деление врёт.
  //
  // Ищем u = p + q·x с u² = a + b·x. Пусть v — сопряжённое по расширению.
  // Тогда u·v = ±n, где n² = N(a+bx), а (u+v)² = u² + v² + 2uv = 2a + bS ± 2n.
  // Если s = u+v нашлось в базовом поле, то из 2pq + q²S = b сразу q = b/s,
  // а p = (s² − bS)/(2s). Ответ проверяется возведением в квадрат.
  sqrt() {
    const { S, Q } = this.ext;
    if (this.b.isZero()) {
      const inner = this.a.sqrt?.();
      if (inner) return new Alg(this.ext, inner, this.b);

      // Второй случай, который легко проглядеть: у элемента БАЗЫ корень может
      // лежать не в базе, а иметь ненулевую часть при x.
      //
      // Из (p + q·x)² = a следует 2p + q·S = 0, то есть p = −qS/2, и тогда
      // q² = 4a/(S²−4Q). Проглядеть это дорого: именно так связаны середины
      // дуг (u² = bc, v² = ca, w² = ab, откуда √(ab) = ±uv/c). Без этой ветви
      // движок не замечает, что третий корень уже лежит в поле первых двух, и
      // строит поле вдвое больше настоящего — а в нём тождества, держащиеся на
      // связи корней, перестают выполняться.
      const disc = S.mul(S).sub(Q.mul(4n));
      if (disc.isZero()) return null;
      const q = this.a.mul(4n).div(disc).sqrt?.();
      if (!q) return null;
      const p = q.mul(S).div(-2n);
      const candidate = new Alg(this.ext, p, q);
      return candidate.mul(candidate).equals(this) ? candidate : null;
    }
    // Дешёвый отсев ДО нормы. Норма — это несколько умножений больших дробей,
    // и на реальной задаче (прямая через точку на касательной, пересечённая с
    // окружностью) она одна считалась минутами. А проверяется разложимость у
    // КАЖДОГО квадратного уравнения, и ответ почти всегда «не квадрат».
    //
    // Если a + b·x — квадрат, то и его норма квадрат, а значит её значение в
    // любой точке — квадрат числа. Обратное неверно, но ошибка безопасна:
    // случайно попав в квадрат, мы просто пойдём длинным путём.
    if (!this.#normCouldBeSquare()) return null;
    const n = this.norm().sqrt?.();
    if (!n) return null;
    const half = this.a.mul(2n).add(this.b.mul(S));
    for (const total of [half.add(n.mul(2n)), half.sub(n.mul(2n))]) {
      const s = total.sqrt?.();
      if (!s || s.isZero()) continue;
      const q = this.b.div(s);
      const p = s.mul(s).sub(this.b.mul(S)).div(s.mul(2n));
      const candidate = new Alg(this.ext, p, q);
      if (candidate.mul(candidate).equals(this)) return candidate;
    }
    return null;
  }

  // Приближённое вычисление — для живой сверки с чертежом. Численное значение
  // самого корня берётся не из радикала, а с чертежа: корень ЕСТЬ точка,
  // построенная GeoGebra, и мост кладёт её координаты в ext.numericRoot. Это
  // и надёжнее (никакого выбора ветви), и согласовано с тем, что нарисовано.
  evalFloat(values) {
    const a = this.a.evalFloat(values);
    if (this.b.isZero()) return a;
    const root = rootFloat(this.ext, values);
    if (!root) return { re: NaN, im: NaN };
    const b = this.b.evalFloat(values);
    return {
      re: a.re + (b.re * root.re - b.im * root.im),
      im: a.im + (b.re * root.im + b.im * root.re),
    };
  }

  // Норма в одной числовой точке: N = a² + a·b·S + b²·Q. Считается по числам,
  // а не по многочленам, поэтому стоит ничего. false — значит квадрата точно
  // нет; true — «может быть», и дальше идёт честный путь.
  //
  // На башне (когда коэффициенты сами лежат в расширении) проверку пропускаем:
  // числового значения у присоединённого корня тут нет, а врать нельзя.
  #normCouldBeSquare() {
    const { S, Q } = this.ext;
    for (const part of [this.a, this.b, S, Q]) {
      if (part.isAlg || typeof part.evalAt !== 'function') return true;
    }
    const size = this.a.ring?.size ?? 0;
    if (!size) return true;
    for (let attempt = 0; attempt < 3; attempt++) {
      const values = [];
      for (let v = 0; v < size; v++) values.push(new CFrac(BigInt(2 + v * 3 + attempt * 7)));
      try {
        const a = this.a.evalAt(values), b = this.b.evalAt(values);
        const s = S.evalAt(values), q = Q.evalAt(values);
        const n = a.mul(a).add(a.mul(b).mul(s)).add(b.mul(b).mul(q));
        if (n.re.isZero() && n.im.isZero()) continue;      // ноль ничего не говорит
        return !!sqrtCFrac(n);
      } catch {
        continue;                                          // знаменатель обнулился — другая точка
      }
    }
    return true;
  }

  // Нужен печати уравнений: решает, брать ли коэффициент в скобки. Значение с
  // корнем — сумма двух слагаемых, так что просто оно быть не может.
  isSimple() { return this.b.isZero() && (this.a.isSimple?.() ?? false); }

  // Лежит ли значение в базовом поле — тогда его можно вернуть наружу как
  // обычную рациональную функцию и забыть про расширение.
  isRational() { return this.b.isZero() && (this.a.isRational?.() ?? true); }
  toRational() {
    if (!this.isRational()) throw new Error('Alg: значение иррационально');
    return this.a;
  }

  #render(str, name, times) {
    if (this.b.isZero()) return str(this.a);
    const base = this.b.ring;
    // Минус выносим в знак, а единичный коэффициент не пишем вовсе:
    // «a + (-1)·t» и «a + -2·t» читаются заметно хуже, чем «a − t» и «a − 2·t».
    let sign = '+';
    let coeff = this.b;
    let text = str(coeff);
    if (text.startsWith('-') || text.startsWith('−')) {
      sign = '−';
      coeff = coeff.neg();
      text = str(coeff);
    }

    const root = coeff.equals(base.one())
      ? name
      : `${coeff.isSimple?.() ? text : `(${text})`}${times}${name}`;
    if (this.a.isZero()) return sign === '−' ? `−${root}` : root;
    return `${str(this.a)} ${sign} ${root}`;
  }

  toString() { return this.#render(r => r.toString(), this.ext.name, '·'); }
  // Обратный слэш обязан быть удвоен: '\cdot' в JS — это просто «cdot», слэш
  // теряется молча, и KaTeX печатает «cdott» вместо знака умножения.
  // У корня может быть отдельная запись для формул: «√3S» в обычном тексте
  // читается, а в TeX должно стоять \sqrt{3}, иначе получается набор букв.
  toTex() { return this.#render(r => r.toTex(), this.ext.texName ?? this.ext.name, ' \\cdot '); }
}
