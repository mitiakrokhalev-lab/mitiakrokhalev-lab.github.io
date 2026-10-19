// Многочлен над конечным полем в УПАКОВАННОМ виде — рабочая лошадка
// модулярного НОДа.
//
// Почему не общий `poly.js`. Он универсален: одночлен — массив показателей,
// коэффициент — объект с методами. Для алгебры движка это правильно, а для
// модулярного НОДа — разорительно: там миллионы крошечных многочленов, и замер
// показал 446 микросекунд на узел рекурсии при входе в 29 членов, то есть
// пятнадцать микросекунд на ОДИН ЧЛЕН. Время уходило не в арифметику, а в
// аллокацию массивов показателей, объектов-коэффициентов и записей карты, и
// профиль был размазан ровным слоем по всему — верный признак того, что дело в
// представлении, а не в алгоритме.
//
// Здесь:
//   * одночлен — ОДНО ЧИСЛО: показатели сложены битовыми полями;
//   * коэффициент — ОДНО ЧИСЛО: пара (re, im) сложена как re·p + im (fp2.js);
//   * сам многочлен — Map<число, число>, без единого объекта внутри.
//
// Ширина поля показателей считается по фактическим степеням задачи, с запасом
// на удвоение (произведения и интерполянт растут, но не больше чем вдвое).
// Если не влезает в 52 бита — честно отвечаем «не мой случай», и НОД считается
// прежним путём. На практике не влезть трудно: пять переменных степени девять
// занимают 23 бита.

import { checkIfHeavy } from './budget.js';

// Раскладка показателей: сколько места на какую переменную и как её доставать.
// vars — индексы переменных ИСХОДНОГО кольца, позиция в этом списке и есть
// номер разряда.
//
// Основание разряда берётся ТОЧНЫМ, а не округлённым вверх до степени двойки.
// Сначала было по-битовому, и это стоило до половины ёмкости на каждой
// переменной: показателю до 9 хватает основания 10, а битовое поле выделяло 16.
// На пяти буквах разница незаметна, а на пятнадцати решает, влезет задача или
// уйдёт в запасной путь. Код от этого не изменился ни на строку — он с самого
// начала написан через `scale` и `cap`, то есть в смешанной системе счисления;
// степенями двойки они были только по привычке.
//
// Потолок — 2^52: ключи сравниваются и СКЛАДЫВАЮТСЯ (умножение многочленов
// складывает показатели), а точными целые остаются до 2^53.
const KEY_CAPACITY = Math.pow(2, 52);

// Потолок раскладки достигнут. Отдельный класс, а не просто ошибка: это не
// поломка и не «не поддержано», а честная граница движка, и пользователю надо
// сказать именно это. Раньше здесь был молчаливый обход — счёт уходил в старый
// путь, который на таких задачах молол часами; лучше внятная строка.
export class CeilingExceeded extends Error {
  constructor(vars, degree) {
    super(`превышен потолок движка: ${vars} букв в одном выражении при степенях `
      + `до ${degree} — показатели перестают помещаться в одночлен. `
      + 'Попробуйте разбить построение на части.');
    this.name = 'CeilingExceeded';
    this.vars = vars;
    this.degree = degree;
  }
}

export function makePacking(vars, budgets) {
  const n = vars.length;
  const scale = new Array(n);
  const cap = new Array(n);
  let used = 1;
  for (let j = 0; j < n; j++) {
    scale[j] = used;
    cap[j] = budgets[j] + 1;
    used *= cap[j];
    if (used > KEY_CAPACITY) return null;   // показатели не влезли
  }
  return { vars, n, scale, cap };
}

// ---- многочлены как ПЛОСКИЕ МАССИВЫ над полем ------------------------------
//
// Одномерный слой, на котором стоят и двупеременные узлы, и разреженная
// интерполяция: коэффициент по индексу степени, ничего лишнего.

export const trimArr = a => { while (a.length > 0 && !a[a.length - 1]) a.pop(); return a; };

// Значение многочлена в точке — схема Горнера.
export function evalArray(F, arr, x) {
  let acc = 0;
  for (let i = arr.length - 1; i >= 0; i--) acc = F.add(F.mul(acc, x), arr[i] ?? 0);
  return acc;
}

export function scaleArray(F, arr, c) {
  const out = new Array(arr.length);
  for (let i = 0; i < arr.length; i++) out[i] = F.mul(arr[i] ?? 0, c);
  return out;
}

export function subArray(F, a, b) {
  const n = Math.max(a.length, b.length);
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = F.sub(a[i] ?? 0, b[i] ?? 0);
  return trimArr(out);
}

export function addArrayInto(F, target, other) {
  for (let i = 0; i < other.length; i++) target[i] = F.add(target[i] ?? 0, other[i] ?? 0);
  while (target.length < other.length) target.push(0);
  return target;
}

// Умножение на (x − α): база Ньютона растёт по одной точке за шаг.
export function mulByLinear(F, arr, alpha) {
  const out = new Array(arr.length + 1).fill(0);
  for (let i = 0; i < arr.length; i++) {
    const c = arr[i] ?? 0;
    if (!c) continue;
    out[i + 1] = F.add(out[i + 1], c);
    out[i] = F.sub(out[i], F.mul(c, alpha));
  }
  return trimArr(out);
}

// Подстановка вместо переменной СТРОК — тот же Горнер, только коэффициенты
// сами многочлены (строки).
export function evalRows(F, rows, alpha) {
  let acc = [];
  for (let e = rows.length - 1; e >= 0; e--) {
    if (acc.length > 0) acc = scaleArray(F, acc, alpha);
    const row = rows[e];
    if (row && row.length) acc = addArrayInto(F, acc, row);
  }
  return trimArr(acc);
}

// interp += basis(строки) ⊗ err(столбцы): внешнее произведение, потому что один
// множитель зависит только от переменной подстановки, а другой — только от
// второй.
export function addOuter(F, interp, basis, err) {
  for (let i = 0; i < basis.length; i++) {
    const b = basis[i] ?? 0;
    if (!b) continue;
    let row = interp[i];
    if (!row) row = interp[i] = [];
    for (let j = 0; j < err.length; j++) {
      const e = err[j] ?? 0;
      if (!e) continue;
      row[j] = F.add(row[j] ?? 0, F.mul(b, e));
    }
  }
}



// Одномерный слой ФАБРИКОЙ по полю, а не набором функций с полем в аргументе.
//
// Разница не косметическая: сначала эти функции лежали просто в модуле и брали
// поле параметром — и горячий путь НОДа замедлился вдвое (373 → 845 мс на
// эталонной задаче). Замыкание позволяет движку специализировать код под
// конкретное поле, а параметр — нет. Реализация при этом по-прежнему ОДНА:
// и модулярный НОД, и факторизация берут её отсюда.
export function arrayOps(F) {
  // Остаток от деления одномерных над полем.
  function remArray(a, b) {
    const db = b.length - 1;
  const inv = F.inv(b[db]);
  const r = a.slice();
  while (r.length - 1 >= db && r.length > 0) {
    const factor = F.mul(r[r.length - 1], inv);
    const shift = r.length - 1 - db;
    for (let i = 0; i <= db; i++) r[i + shift] = F.sub(r[i + shift], F.mul(factor, b[i]));
    while (r.length > 0 && r[r.length - 1] === 0) r.pop();
  }
  return r;
  }

  // Одномерный НОД, приведённый к моническому виду.
  function gcdArray(a, b) {
  checkIfHeavy(a.length * b.length);
  a = a.slice();
  b = b.slice();
  while (b.length > 0) {
    const r = remArray(a, b);
    a = b;
    b = r;
  }
  if (a.length === 0) return [F.one];
  const inv = F.inv(a[a.length - 1]);
  return a.map(c => F.mul(c, inv));
  }

  // Точное деление одномерных: null, если остаток ненулевой.
  function divideArray(a, b) {
  const db = b.length - 1;
  if (a.length === 0) return [];
  if (a.length - 1 < db) return null;
  const inv = F.inv(b[db]);
  const rem = a.slice();
  const quot = new Array(a.length - db).fill(0);
  for (let k = rem.length - 1; k >= db; k--) {
    const lead = rem[k];
    if (!lead) continue;
    const factor = F.mul(lead, inv);
    quot[k - db] = factor;
    for (let i = 0; i <= db; i++) rem[k - db + i] = F.sub(rem[k - db + i] ?? 0, F.mul(factor, b[i]));
  }
  for (let i = 0; i < db; i++) if (rem[i]) return null;
  return trimArr(quot);
  }

  // Произведение одномерных — школьное, длины здесь десятки.
  function mulArray(a, b) {
  if (a.length === 0 || b.length === 0) return [];
  checkIfHeavy(a.length * b.length);
  const out = new Array(a.length + b.length - 1).fill(0);
  for (let i = 0; i < a.length; i++) {
    const ai = a[i];
    if (!ai) continue;
    for (let j = 0; j < b.length; j++) {
      if (!b[j]) continue;
      out[i + j] = F.add(out[i + j], F.mul(ai, b[j]));
    }
  }
  return trimArr(out);
  }

  return { remArray, gcdArray, divideArray, mulArray };
  }

export function makeOps(F, packing) {
  const { n, scale, cap } = packing;
  const { gcdArray, divideArray } = arrayOps(F);

  const expOf = (key, j) => Math.floor(key / scale[j]) % cap[j];
  const clearVar = (key, j) => key - expOf(key, j) * scale[j];

  // Полная степень одночлена — с пропуском одной переменной (skip = −1, если
  // пропускать нечего). Порядок тот же, что у P.compareExp: сначала полная
  // степень, потом показатели по переменным. Он мультипликативен, и на этом
  // держится вся работа со старшими коэффициентами в modgcd.js.
  function totalDegree(key, skip) {
    let sum = 0;
    for (let j = 0; j < n; j++) {
      if (j === skip) continue;
      sum += Math.floor(key / scale[j]) % cap[j];
    }
    return sum;
  }

  // Сравнение одночленов: отрицательное — первый СТАРШЕ.
  function compare(x, y, skip) {
    const dx = totalDegree(x, skip), dy = totalDegree(y, skip);
    if (dx !== dy) return dy - dx;
    for (let j = 0; j < n; j++) {
      if (j === skip) continue;
      const a = Math.floor(x / scale[j]) % cap[j];
      const b = Math.floor(y / scale[j]) % cap[j];
      if (a !== b) return b - a;
    }
    return 0;
  }

  function addInto(map, key, coeff) {
    if (coeff === 0) return;
    const cur = map.get(key);
    if (cur === undefined) { map.set(key, coeff); return; }
    const sum = F.add(cur, coeff);
    if (sum === 0) map.delete(key);
    else map.set(key, sum);
  }

  function add(x, y) {
    checkIfHeavy(x.size + y.size);
    const out = new Map(x);
    for (const [key, coeff] of y) addInto(out, key, coeff);
    return out;
  }

  function sub(x, y) {
    checkIfHeavy(x.size + y.size);
    const out = new Map(x);
    for (const [key, coeff] of y) addInto(out, key, F.neg(coeff));
    return out;
  }

  // Умножение — единственное место, где одна операция может занять сколько
  // угодно: пар членов тут произведение размеров. Без проверки бюджета ИМЕННО
  // ЗДЕСЬ обещание «не посчитано за пять секунд» становится враньём — счёт
  // уходит внутрь одного умножения, а проверки стоят уровнем выше и до них
  // очередь доходит уже сильно позже срока.
  function mul(x, y) {
    checkIfHeavy(x.size * y.size);
    const out = new Map();
    for (const [kx, cx] of x) {
      for (const [ky, cy] of y) addInto(out, kx + ky, F.mul(cx, cy));
    }
    return out;
  }

  function scaleBy(x, coeff) {
    const out = new Map();
    if (coeff === 0) return out;
    for (const [key, c] of x) out.set(key, F.mul(c, coeff));
    return out;
  }

  // Умножение на x_j^k — показатели правятся прямо в ключе.
  function shiftVar(x, j, k) {
    if (k === 0) return x;
    const out = new Map();
    const delta = k * scale[j];
    for (const [key, c] of x) out.set(key + delta, c);
    return out;
  }

  function degreeIn(x, j) {
    let d = 0;
    for (const key of x.keys()) {
      const e = Math.floor(key / scale[j]) % cap[j];
      if (e > d) d = e;
    }
    return d;
  }

  // Старший одночлен (по полному порядку либо с пропуском переменной).
  function leadKey(x, skip = -1) {
    let best = -1;
    for (const key of x.keys()) {
      if (best < 0 || compare(key, best, skip) < 0) best = key;
    }
    return best;
  }

  function leadCoeff(x) {
    const key = leadKey(x, -1);
    return key < 0 ? 0 : x.get(key);
  }

  // Старший коэффициент по ОСТАЛЬНЫМ переменным: многочлен от одной x_j.
  function leadIn(x, j) {
    const best = leadKey(x, j);
    const out = new Map();
    if (best < 0) return out;
    for (const [key, c] of x) {
      if (compare(key, best, j) !== 0) continue;
      out.set(expOf(key, j) * scale[j], c);
    }
    return out;
  }

  // Приведение старшего коэффициента к единице.
  function monic(x) {
    const lead = leadCoeff(x);
    if (lead === 0 || lead === F.one) return x;
    return scaleBy(x, F.inv(lead));
  }

  // Подстановка значения вместо одной переменной.
  function evalVar(x, j, alpha) {
    checkIfHeavy(x.size);
    const deg = degreeIn(x, j);
    if (deg === 0) return x;
    const powers = [F.one];
    for (let k = 1; k <= deg; k++) powers[k] = F.mul(powers[k - 1], alpha);
    const out = new Map();
    for (const [key, c] of x) {
      const e = Math.floor(key / scale[j]) % cap[j];
      addInto(out, key - e * scale[j], e === 0 ? c : F.mul(c, powers[e]));
    }
    return out;
  }

  // Взгляд на многочлен как на многочлен от x_j: массив коэффициентов, каждый
  // из которых — многочлен без x_j.
  function coeffsIn(x, j) {
    checkIfHeavy(x.size);
    const out = [];
    for (const [key, c] of x) {
      const e = Math.floor(key / scale[j]) % cap[j];
      while (out.length <= e) out.push(new Map());
      out[e].set(key - e * scale[j], c);
    }
    return out;
  }

  // Точное деление; null, если не делится нацело.
  //
  // Делим СТОЛБИКОМ по коэффициентам при степенях главной переменной, а не по
  // многочленам целиком. Разница не косметическая: прежняя версия на каждом
  // шаге заново разбирала весь остаток на коэффициенты и заново вычитала
  // произведение по всему многочлену, и профиль показывал в этой паре
  // (`coeffsIn` + `sub`) пятую часть всего времени НОДа. Здесь разбор делается
  // один раз, а вычитание идёт только по тем коэффициентам, которых оно
  // касается.
  function divideExact(A, B) {
    if (B.size === 0) return null;
    if (A.size === 0) return new Map();
    const j = mainVar(B);
    if (j < 0) return scaleBy(A, F.inv(B.get(0)));

    const bs = coeffsIn(B, j);
    const db = bs.length - 1;
    const lb = bs[db];
    const rem = coeffsIn(A, j);
    const da = rem.length - 1;
    if (da < db) return null;

    const quot = new Array(da - db + 1);
    for (let k = da; k >= db; k--) {
      const cur = rem[k];
      if (!cur || cur.size === 0) { quot[k - db] = null; continue; }
      const t = divideExact(cur, lb);
      if (!t) return null;
      quot[k - db] = t;
      for (let i = 0; i <= db; i++) {
        if (bs[i].size === 0) continue;
        const at = k - db + i;
        rem[at] = sub(rem[at] ?? new Map(), mul(t, bs[i]));
      }
    }
    // Хвост обязан обнулиться: иначе деление не точное.
    for (let k = 0; k <= da; k++) if (rem[k] && rem[k].size > 0) return null;

    let out = new Map();
    for (let k = 0; k < quot.length; k++) {
      if (quot[k] && quot[k].size > 0) out = add(out, shiftVar(quot[k], j, k));
    }
    return out;
  }

  // Старшая переменная, реально входящая в многочлен.
  function mainVar(x) {
    let top = -1;
    for (const key of x.keys()) {
      for (let j = n - 1; j > top; j--) {
        if (Math.floor(key / scale[j]) % cap[j] > 0) { top = j; break; }
      }
    }
    return top;
  }

  // ---- одномерный слой -----------------------------------------------------
  //
  // Дно рекурсии, куда приходит каждая точка подстановки. Здесь многочлен —
  // просто массив коэффициентов поля.

  function toArray(x, j) {
    const out = [];
    for (const [key, c] of x) {
      const e = Math.floor(key / scale[j]) % cap[j];
      while (out.length <= e) out.push(0);
      out[e] = F.add(out[e], c);
    }
    while (out.length > 0 && out[out.length - 1] === 0) out.pop();
    return out;
  }

  function fromArray(arr, j) {
    const out = new Map();
    for (let e = 0; e < arr.length; e++) {
      if (arr[e] !== 0) out.set(e * scale[j], arr[e]);
    }
    return out;
  }

  // Одномерный слой общий (см. выше): здесь только привязка к своему полю,
  // чтобы у арифметики массивов была РОВНО ОДНА реализация.

  function isOne(x) {
    return x.size === 1 && x.get(0) === F.one;
  }

  function constant(coeff) {
    const out = new Map();
    if (coeff !== 0) out.set(0, coeff);
    return out;
  }

  // Одночлен x_j (нужен для базиса Ньютона).
  function variable(j) {
    return new Map([[scale[j], F.one]]);
  }

  return {
    F,
    packing,
    expOf,
    clearVar,
    compare,
    add,
    sub,
    mul,
    scaleBy,
    shiftVar,
    degreeIn,
    leadKey,
    leadCoeff,
    leadIn,
    monic,
    evalVar,
    coeffsIn,
    divideExact,
    mainVar,
    toArray,
    fromArray,
    gcdArray,
    divideArray,
    isOne,
    constant,
    variable,
    keyExps(key) {
      const exps = [];
      for (let j = 0; j < n; j++) exps.push(Math.floor(key / scale[j]) % cap[j]);
      return exps;
    },
  };
}
