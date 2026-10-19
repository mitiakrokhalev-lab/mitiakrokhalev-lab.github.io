import { ComplanatorBridge } from '../src/geogebra/bridge.js';
import { t, lang, setLang, savedLang, applyLang, onLang } from '../src/lang/i18n.js';

// ПЛАТНЫЕ ДВИЖКИ ПРИХОДЯТ ПО ПРАВУ, А НЕ ВМЕСТЕ СО СТРАНИЦЕЙ.
//
// Раньше Бариканатор и генератор стояли здесь обычными импортами — и это
// значит, что их код уезжал в браузер КАЖДОМУ посетителю, а закрыты они были
// атрибутом hidden на кнопке. Такой запрет снимается в инспекторе за две
// секунды, то есть платного в нём не было ничего.
//
// Теперь модуль приходит по требованию и только тому, у кого право открыто:
// сайт просит его у базы с токеном сессии (см. paidModule в account.js).
// Тот, кто не платил, кода не получает вовсе — и это единственный запрет,
// который в браузерном приложении вообще может работать.
//
// ЗАОДНО ЭТО ЧИСТИТ ОДНОФАЙЛОВУЮ СБОРКУ. Сборщик идёт по статическим импортам,
// динамических не видит — поэтому платное в «Крополятор.html» больше не
// попадает. А попадать не должно: файл без сети проверить право не может, и
// скачанная копия с платными движками была бы разовой покупкой вместо
// подписки, которую незачем продлевать.
//
// Имена объявлены здесь и заполняются при загрузке — так все обращения к ним
// ниже (а их около сотни) остались ровно такими, какими были.
let BarikanatorBridge;
let estimate, searchCost, probe, PROBE_CAP, FULL_SEARCH_POINTS;
let worldFromBridge, OPS, KIND, PREDICATES, generate, substance;
let generalizeFact, redundantGivens, generalizeMetric, recheckFact;
let statement, problemText, conditionsOf, withSubscripts;
let planFact, drawingValues, StopToken;
let withVocabulary, EN;

// Числа в панели — с разрядами: «4 659 344 140» читается, «4659344140» нет.
const nice = n => Number(n).toLocaleString('ru-RU');
// «2 221 объектов» режет глаз, а число там всякий раз разное.
const plural = (n, one, few, many) => {
  const a = Math.abs(Math.round(n)) % 100, b = a % 10;
  if (a > 10 && a < 20) return many;
  if (b === 1) return one;
  if (b >= 2 && b <= 4) return few;
  return many;
};

const rowsEl = document.getElementById('rows');
const emptyMsg = document.getElementById('empty-msg');
const statusEl = document.getElementById('status');
const rowElements = new Map();
// Строки, у которых пользователь переключил вид уравнения на канонический.
// Держим это здесь, а не в самой строке: renderRow зовётся на каждое обновление
// объекта (в том числе при перетаскивании), и выбор не должен слетать.
const canonicalRows = new Set();

function renderRow(name, info) {
  emptyMsg.style.display = 'none';
  let tr = rowElements.get(name);
  if (!tr) {
    tr = document.createElement('tr');
    rowElements.set(name, tr);
    rowsEl.appendChild(tr);
  }
  tr.className = info.kind === 'point' ? '' : info.kind;
  // сырая команда GeoGebra — видна во всплывающей подсказке, чтобы было понятно,
  // что именно движок пытался разобрать
  if (info.raw) tr.title = info.raw; else tr.removeAttribute('title');
  tr.innerHTML = `<td class="name">${escapeHtml(name)}</td><td class="formula"></td>`;
  const cell = tr.querySelector('.formula');
  const canonical = !!info.canonical && canonicalRows.has(name);
  // Канонический вид считается только когда его правда показывают: это лишнее
  // разложение на множители, а перерисовка идёт на каждое движение мыши.
  const shown = canonical ? info.canonical() : info;
  if (info.kind === 'pending') {
    // Счёт не уложился в бюджет. Это не поломка: ответ есть, он просто дорогой,
    // и ждать его или нет — решает пользователь. Поэтому не молчаливое
    // подвисание и не «ошибка», а честная строка с кнопкой и оценкой.
    cell.textContent = info.text;
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'canon compute';
    button.textContent = t('посчитать');
    button.title = `полный счёт: ${info.estimate}`;
    button.addEventListener('click', () => {
      button.disabled = true;
      button.textContent = t('считаю…');
      // Даём браузеру перерисоваться: счёт синхронный и надолго заберёт поток,
      // иначе кнопка так и останется в прежнем виде до самого конца.
      setTimeout(() => {
        const started = Date.now();
        try {
          info.compute();
        } catch (e) {
          cell.textContent = `ошибка: ${e.message}`;
        }
        const spent = Math.round((Date.now() - started) / 1000);
        const note = document.createElement('span');
        note.className = 'note';
        note.textContent = `посчитано за ${spent} с`;
        rowElements.get(name)?.querySelector('.formula')?.appendChild(note);
      }, 30);
    });
    cell.appendChild(button);
    const hint = document.createElement('span');
    hint.className = 'note';
    hint.textContent = info.estimate;
    cell.appendChild(hint);
  } else if (info.kind === 'unsupported') {
    cell.textContent = info.text;
  } else {
    const value = document.createElement('span');
    try {
      window.katex.render(shown.tex ?? shown.text, value, { throwOnError: false });
    } catch {
      value.textContent = shown.text;
    }
    cell.appendChild(value);
  }
  // ЧИСТЫЙ ТЕКСТ ФОРМУЛЫ — ОТДЕЛЬНО ОТ РАЗМЕТКИ.
  //
  // KaTeX кладёт в ячейку сразу три вида записи: видимую вёрстку, невидимый
  // MathML и исходный TeX в annotation. Прочитать ячейку текстом — получить
  // всё это подряд, да ещё с подписью кнопки: в выгрузке выходило «aaa» вместо
  // «a» и «z+abz¯=a+bz + a b ar{z} = …кан.» вместо уравнения прямой.
  // Поэтому исходную строку кладём рядом, и выгрузка берёт её.
  cell.dataset.plain = (info.kind === 'pending' || info.kind === 'unsupported'
    ? info.text : (shown.text ?? '')) ?? '';
  // Нормированный вид единствен и потому удобен движку, а на бумаге привычнее
  // общий — поэтому переключатель, а не замена.
  if (info.canonical) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'canon';
    button.textContent = canonical ? t('норм.') : t('кан.');
    button.title = canonical
      ? 'вернуть нормированный вид'
      : 'привести к общему виду: A·z + B·z̄ + C = 0';
    button.addEventListener('click', () => {
      if (canonical) canonicalRows.delete(name); else canonicalRows.add(name);
      renderRow(name, info);
    });
    cell.appendChild(button);
  }
  // правило сопряжения образующей — объясняет, почему в ответах не всплывают
  // лишние буквы
  if (info.note) {
    const note = document.createElement('span');
    note.className = 'note';
    note.textContent = info.note;
    cell.appendChild(note);
  }
  // живая сверка: символьный ответ подставлен в настоящие координаты чертежа
  if (info.check) {
    const bad = document.createElement('span');
    bad.className = 'note mismatch';
    bad.textContent = info.check;
    cell.appendChild(bad);
  }
}

function removeRow(name) {
  const tr = rowElements.get(name);
  if (tr) { tr.remove(); rowElements.delete(name); }
  canonicalRows.delete(name);
}

// ---- замер счёта ----------------------------------------------------------
//
// Показываем в панели, а не в консоли. Консоль тут бесполезна: пока вкладка
// занята счётом, она ничего не выводит, а разбираться надо именно в этот
// момент. Плюс это надёжный маркер версии — строка либо есть, либо нет.
// Штамп сборки: в однофайловой версии его проставляет сборщик, в исходниках он
// так и остаётся заглушкой. Нужен, чтобы отличать «не помогло» от «запущена
// старая версия» — это разные диагнозы.
const BUILD_STAMP = 'СБОРКА-НЕ-ПРОСТАВЛЕНА';
const BUILD_LABEL = BUILD_STAMP.startsWith('СБОРКА') ? 'из исходников' : `сборка ${BUILD_STAMP}`;

const diagEl = document.getElementById('diag');
// Показываем, ЧТО именно открыто, не дожидаясь первого счёта: иначе понять,
// свежая ли это версия или браузер отдал старую из кэша, попросту нечем.
if (diagEl) diagEl.textContent = `${BUILD_LABEL} · счёт: пока нечего мерить`;
let diagPending = false;

function scheduleDiag() {
  if (diagPending || !diagEl) return;
  diagPending = true;
  // После того как поток освободится: пока идёт счёт, перерисовывать нечем.
  setTimeout(() => {
    diagPending = false;
    const all = [...engine.timings].filter(([, ms]) => ms > 0);
    // Число образующих — главный множитель стоимости: каждая новая буква
    // умножает размер выражений. Если их больше, чем ожидаешь по чертежу,
    // значит в файле остались объекты от прошлых опытов — и считается совсем
    // не та задача, которую видишь.
    const letters = `${engine.ring.size} букв (${engine.ring.names.join(',')})`;
    if (all.length === 0) {
      diagEl.textContent = `${BUILD_LABEL} · ${letters} · счёт: всё мгновенно`;
      return;
    }
    const total = all.reduce((s, [, ms]) => s + ms, 0);
    const [slowName, slowMs] = all.reduce((x, y) => (y[1] > x[1] ? y : x));
    diagEl.textContent =
      `${BUILD_LABEL} · ${letters} · счёт: всего ${total} мс, дольше всех ${slowName} — ${slowMs} мс`;
  }, 0);
}

// Два движка над одним чертежом. Слушает события только АКТИВНЫЙ: пересчитывать
// оба всё время вдвое дороже, а второй ответ в это время всё равно не виден.
// Расплата — при переключении построение приходится перечитать заново; оно того
// стоит, потому что перетаскивание вершины идёт куда чаще, чем смена движка.
const handlers = {
  onRow: (name, info) => { renderRow(name, info); scheduleDiag(); },
  onRemove: removeRow,
};

const ENGINES = {
  complex: { bridge: new ComplanatorBridge(handlers), label: 'Компланатор', hint: 'через a, b, c на единичной окружности' },
  // Мост Бариканатора строится НЕ ЗДЕСЬ, а когда право на него подтвердится:
  // до того его кода в браузере нет вовсе (см. loadBary ниже).
  bary: { bridge: null, label: 'Бариканатор', hint: 'барицентрика относительно ABC' },
};

let engineKey = 'complex';
let engine = ENGINES.complex.bridge;
// Чего человек хотел в прошлый раз. Применяется не сразу: платный движок надо
// сперва получить, а право на него база подтверждает позже самой страницы.
let wantedEngine = 'complex';

// для отладки из консоли
window.complanator = ENGINES.complex.bridge;

// ---- платные модули --------------------------------------------------------
//
// За модулем ходит account.js: токен сессии живёт там, и ему отвечает база.
// Здесь только склейка — и забота о том, чтобы один и тот же модуль не
// скачивался дважды.
let accountModule = null;   // появляется, когда поднялся account.js

const paidModule = what => {
  if (!accountModule) throw new Error('нет связи с учётными записями');
  return accountModule.paidModule(what);
};

// НЕУДАЧНАЯ ПОПЫТКА НЕ ЗАПОМИНАЕТСЯ. Если оставить в переменной отказавшее
// обещание, один мигнувший интернет закроет движок до перезагрузки страницы —
// а причина того не стоит. Удачная запоминается: второй раз качать незачем.
const once = (hold, make) => {
  if (hold.p) return hold.p;
  hold.p = make().catch(e => { hold.p = null; throw e; });
  return hold.p;
};

const baryHold = {};
function loadBary() {
  return once(baryHold, async () => {
    ({ BarikanatorBridge } = await paidModule('bary'));
    ENGINES.bary.bridge = new BarikanatorBridge(handlers);
    window.barikanator = ENGINES.bary.bridge;   // для отладки из консоли
    return ENGINES.bary.bridge;
  });
}

// Выгрузка задачи — тоже платная, и по той же причине, а не по прихоти: она
// пишет условие словами, то есть тянет statement.js, а с ним по замыканию
// двадцать модулей генератора из двадцати девяти. Отделить нельзя, поэтому
// она входит в тариф генератора (см. шапку src/paid/export.js).
const exportHold = {};
const loadExport = () => once(exportHold, () => paidModule('export'));

const genHold = {};
function loadGen() {
  return once(genHold, async () => {
    ({
      estimate, searchCost, probe, PROBE_CAP, FULL_SEARCH_POINTS,
      worldFromBridge, OPS, KIND, PREDICATES, generate, substance,
      generalizeFact, redundantGivens, generalizeMetric, recheckFact,
      statement, problemText, conditionsOf, withSubscripts,
      planFact, drawingValues, StopToken,
      withVocabulary, EN,
    } = await paidModule('gen'));
  });
}

// ---- ширина панели --------------------------------------------------------
// Апплет живёт в iframe и во время перетаскивания перехватывал бы указатель,
// поэтому ловим события на всём документе и на время тяги гасим у него
// pointer-events (класс body.resizing в стилях).
const WIDTH_KEY = 'complanator:panelWidth';

function setupSplitter() {
  const splitter = document.getElementById('splitter');
  const panel = document.getElementById('panel');
  const saved = localStorage.getItem(WIDTH_KEY);
  if (saved) panel.style.setProperty('--panel-width', saved);

  let dragging = false;
  const apply = clientX => {
    const width = Math.min(Math.max(window.innerWidth - clientX, 220), window.innerWidth * 0.7);
    const value = `${Math.round(width)}px`;
    panel.style.setProperty('--panel-width', value);
    localStorage.setItem(WIDTH_KEY, value);
  };

  splitter.addEventListener('pointerdown', e => {
    dragging = true;
    splitter.classList.add('dragging');
    document.body.classList.add('resizing');
    splitter.setPointerCapture(e.pointerId);
    e.preventDefault();
  });
  splitter.addEventListener('pointermove', e => { if (dragging) apply(e.clientX); });
  const stop = () => {
    if (!dragging) return;
    dragging = false;
    splitter.classList.remove('dragging');
    document.body.classList.remove('resizing');
    // апплет сам не замечает смены размера контейнера
    window.ggbApplet?.recalculateEnvironments?.();
  };
  splitter.addEventListener('pointerup', stop);
  splitter.addEventListener('pointercancel', stop);
  // двойной клик по разделителю — вернуть треть экрана
  splitter.addEventListener('dblclick', () => {
    panel.style.setProperty('--panel-width', '34%');
    localStorage.removeItem(WIDTH_KEY);
    window.ggbApplet?.recalculateEnvironments?.();
  });
}

// УСТАНОВКА КАК ПРИЛОЖЕНИЯ УБРАНА.
//
// Была лишней сущностью: браузер сам предлагал установить, и «приложение»
// выглядело отдельным продуктом — особенно рядом с платными движками.
//
// Регистрации здесь больше нет, но сам sw.js остался и остаётся надолго: он
// переписан так, чтобы снять себя у тех, кто успел установить. Подробности
// — в его собственной шапке.

// ---- вкладки ----------------------------------------------------------------
// Генератор, задачи, чат и учётная запись стоят наверху панели вкладками, а
// таблица движка — своей вкладкой «Алгебра». Блоки остались теми же
// <details>: права и вход по-прежнему прячут их атрибутом hidden, и вкладка
// прячется вместе со своим блоком. Выбор запоминается.
const TAB_KEY = 'complanator:tab';
function setupTabs() {
  const nav = document.getElementById('tabs');
  if (!nav) return;
  const tabs = [...nav.querySelectorAll('[data-tab]')];
  const views = new Map([...document.querySelectorAll('.tab-view')].map(v => [v.dataset.view, v]));
  const ink = nav.querySelector('.tab-ink');
  const blockOf = name => views.get(name)?.querySelector(':scope > details.tabbed');
  let current = null;
  const moveInk = () => {
    const t = tabs.find(x => x.dataset.tab === current);
    if (!ink || !t || t.hidden) return;
    ink.style.width = `${t.offsetWidth}px`;
    ink.style.transform = `translateX(${t.offsetLeft - nav.scrollLeft}px)`;
  };
  const saved = () => { try { return localStorage.getItem(TAB_KEY); } catch { return null; } };
  const show = (name, remember = true) => {
    const tab = tabs.find(t => t.dataset.tab === name && !t.hidden) ?? tabs.find(t => !t.hidden);
    if (!tab || tab.dataset.tab === current) { moveInk(); return; }
    current = tab.dataset.tab;
    for (const t of tabs) {
      const on = t === tab;
      t.classList.toggle('active', on);
      t.setAttribute('aria-selected', String(on));
      t.tabIndex = on ? 0 : -1;
    }
    for (const [key, v] of views) {
      v.hidden = key !== current;
      v.classList.toggle('active', key === current);
    }
    const block = blockOf(current);
    if (block) block.open = true;
    moveInk();
    tab.scrollIntoView({ block: 'nearest', inline: 'nearest' });
    if (remember) try { localStorage.setItem(TAB_KEY, current); } catch { /* приватный режим */ }
  };
  // Вкладка видна, пока виден её блок.
  const sync = () => {
    for (const t of tabs) {
      const block = blockOf(t.dataset.tab);
      if (block) t.hidden = block.hidden;
    }
    const here = tabs.find(t => t.dataset.tab === current);
    if (!here || here.hidden) { current = null; show(saved() ?? 'gen', false); }
    else if (saved() && saved() !== current && !tabs.find(t => t.dataset.tab === saved())?.hidden) show(saved(), false);
    else moveInk();
  };
  for (const t of tabs) t.addEventListener('click', () => show(t.dataset.tab));
  nav.addEventListener('keydown', e => {
    if (e.key !== 'ArrowRight' && e.key !== 'ArrowLeft') return;
    const open = tabs.filter(t => !t.hidden);
    const i = open.findIndex(t => t.dataset.tab === current);
    const next = open[(i + (e.key === 'ArrowRight' ? 1 : open.length - 1)) % open.length];
    if (next) { show(next.dataset.tab); next.focus(); }
  });
  nav.addEventListener('scroll', moveInk, { passive: true });
  window.addEventListener('resize', moveInk);
  const watch = new MutationObserver(sync);
  for (const v of views.values()) {
    const block = v.querySelector(':scope > details.tabbed');
    if (block) watch.observe(block, { attributes: true, attributeFilter: ['hidden'] });
  }
  // Вкладка движка зовётся, как его таблица: «Алгебра» или «Барицентрика».
  const title = document.getElementById('panel-title'), label = document.getElementById('tab-algebra');
  if (title && label) {
    const copy = () => { label.textContent = title.textContent; moveInk(); };
    new MutationObserver(copy).observe(title, { childList: true, characterData: true, subtree: true });
    copy();
  }
  sync();
  document.body.classList.add('tabs-ready');
}

// ---- свёрнутые блоки ------------------------------------------------------
// Справка занимала больше места, чем сама таблица, поэтому она свёрнута, а
// консоли можно убрать ту, что сейчас не нужна. Выбор запоминается: иначе
// сворачивать пришлось бы после каждой перезагрузки.
function setupFoldables() {
  for (const block of document.querySelectorAll('details.console, details.legend')) {
    const key = `complanator:open:${block.querySelector('summary')?.textContent.trim().slice(0, 40)}`;
    const saved = localStorage.getItem(key);
    if (saved !== null) block.open = saved === '1';
    block.addEventListener('toggle', () => {
      localStorage.setItem(key, block.open ? '1' : '0');
      // РАСКРЫТЫЙ БЛОК ПОКАЗЫВАЕТСЯ САМ.
      //
      // Панель прокручивается внутри себя, и блок, раскрытый у нижнего края,
      // уезжает за него целиком: щёлкнул — и ничего не произошло, надо ещё и
      // листать. Особенно заметно на телефоне, где панели достаётся полэкрана,
      // а у генератора содержимого на четыре тысячи пикселей.
      //
      // scrollIntoView с 'nearest' двигает ровно настолько, чтобы заголовок
      // оказался виден, и не дёргает панель, когда блок и так на месте.
      if (!block.open) return;
      requestAnimationFrame(() => {
        block.querySelector('summary')?.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
      });
    });
  }
}

// ---- боковая панель GeoGebra ---------------------------------------------
const ALGEBRA_KEY = 'complanator:algebraView';

function setupAlgebraToggle() {
  const button = document.getElementById('toggle-algebra');
  let visible = localStorage.getItem(ALGEBRA_KEY) === '1';

  const apply = () => {
    button.setAttribute('aria-pressed', String(visible));
    // "AG" — алгебра плюс полотно, "G" — только полотно
    window.ggbApplet?.setPerspective?.(visible ? 'AG' : 'G');
    // Строка ввода GeoGebra ходит вместе с панелью: порознь они не нужны.
    window.ggbApplet?.showAlgebraInput?.(visible);
  };
  button.addEventListener('click', () => {
    visible = !visible;
    localStorage.setItem(ALGEBRA_KEY, visible ? '1' : '0');
    apply();
  });
  return apply;
}

// ---- переключение движков --------------------------------------------------
// Активному движку отдаётся всё построение заново: он его ещё не видел (или
// видел до того, как чертёж поменялся). Таблица при этом чистится целиком —
// строки прежнего движка к новому отношения не имеют.
const ENGINE_KEY = 'kropolyator:engine';

function applyEngine(rebuild) {
  const spec = ENGINES[engineKey];
  // МОСТ ОБЯЗАН БЫТЬ ГОТОВ. Платный движок включается только через
  // chooseEngine, который сперва его получает, так что сюда с пустым мостом
  // прийти нечему. Проверка стоит не из вежливости: engine === null уронил бы
  // первую же строку таблицы, и причину пришлось бы искать далеко отсюда.
  if (!spec.bridge) { engineKey = 'complex'; return applyEngine(rebuild); }
  engine = spec.bridge;
  const button = document.getElementById('toggle-engine');
  button.textContent = spec.label;
  button.title = t(spec.hint);
  button.classList.toggle('bary', engineKey === 'bary');
  document.body.classList.toggle('engine-bary', engineKey === 'bary');
  const head = document.getElementById('panel-title');
  if (head) head.textContent = engineKey === 'bary' ? t('Барицентрика') : t('Алгебра');
  // Бегающая точка называется по-разному. У Компланатора это БУКВА её
  // координаты (в таблице точка D стоит как «d»), у Бариканатора — само ИМЯ
  // точки: там координат три, и звать их по одной незачем.
  for (const id of ['calc-var', 'conds-var']) {
    const field = document.getElementById(id);
    if (!field) continue;
    field.placeholder = engineKey === 'bary' ? 'D' : 'd';
    field.title = engineKey === 'bary'
      ? 'независимая точка: её имя на чертеже — по ней и строится ГМТ'
      : 'независимая точка: буква её координаты — по ней и строится ГМТ';
  }
  if (rebuild && window.ggbApplet) {
    for (const name of [...rowElements.keys()]) removeRow(name);
    engine.rebuild(window.ggbApplet);
  }
}

// ВЫБОР ДВИЖКА МОЖЕТ ПОТРЕБОВАТЬ ЕГО СКАЧАТЬ: платный код приходит по праву.
// Поэтому выбор идёт через эту функцию, а applyEngine осталась синхронной и
// работает с уже готовым мостом.
async function chooseEngine(key, rebuild) {
  if (!ENGINES[key]) key = 'complex';
  if (!ENGINES[key].bridge) {
    const button = document.getElementById('toggle-engine');
    if (button) button.disabled = true;
    statusEl.textContent = `${ENGINES[key].label}: получаем…`;
    try {
      // Платный движок пока один. Появится второй — здесь встанет выбор по
      // ключу вместо прямого вызова.
      await loadBary();
    } catch (e) {
      // Сказать вслух. Молчаливое «ничего не произошло» человек прочтёт как
      // поломку кнопки и будет жать её снова.
      statusEl.textContent = `${ENGINES[key].label}: не вышло получить — ${e.message}`;
      return;
    } finally {
      if (button) button.disabled = false;
    }
    statusEl.textContent = 'готов';
  }
  engineKey = key;
  wantedEngine = key;
  try { localStorage.setItem(ENGINE_KEY, key); } catch { /* приватный режим */ }
  applyEngine(rebuild);
}

function setupEngineToggle() {
  // СОХРАНЁННЫЙ ВЫБОР ПРИМЕНЯЕТСЯ НЕ ЗДЕСЬ. Бариканатор платный: его кода в
  // браузере ещё нет, и право на него база подтвердит позже, чем загрузится
  // страница. Поэтому желание запоминается, а исполняет его applyRights.
  const saved = localStorage.getItem(ENGINE_KEY);
  wantedEngine = (saved && ENGINES[saved]) ? saved : 'complex';
  engineKey = 'complex';
  document.getElementById('toggle-engine').addEventListener('click', () => {
    chooseEngine(engineKey === 'complex' ? 'bary' : 'complex', true);
  });
  applyEngine(false);
}

// ---- режим «движок выключен» ----------------------------------------------
// Иногда нужно просто дочертить вспомогательную обвязку, осмысливать которую
// движку незачем. В режиме 2 он её не видит — и продолжает не видеть построенное
// тогда даже после включения: иначе объект вдруг получил бы букву, а его дети,
// построенные раньше, — уже нет.
const MODE_KEY = 'complanator:mode';

function setupModeToggle() {
  const button = document.getElementById('toggle-mode');
  let off = localStorage.getItem(MODE_KEY) === '2';

  const apply = () => {
    engine.setMode(off ? 2 : 1);
    button.textContent = off ? t('движок выключен') : t('движок включён');
    button.classList.toggle('off', off);
    button.setAttribute('aria-pressed', String(off));
    document.body.classList.toggle('engine-off', off);
  };
  // Подпись этой кнопки ставит код, и проход по разметке её не трогает.
  // Перерисовываться она обязана сама: знать про каждую такую кнопку из
  // одного места значит однажды забыть там новую.
  onLang(apply);
  button.addEventListener('click', () => {
    off = !off;
    localStorage.setItem(MODE_KEY, off ? '2' : '1');
    apply();
  });
  apply();
}

// ---- вид объектов на чертеже ----------------------------------------------
//
// Умолчания GeoGebra (точка 5, линия 5) для планиметрии слишком жирные: точек и
// прямых в конфигурации много, и они сливаются в кашу. Поэтому появившийся
// объект получает размер поскромнее — и на этом наше участие кончается.
//
// ДАЛЬШЕ ОФОРМЛЯЕТ САМА GEOGEBRA. Свою панель настроек мы не заводим: у
// GeoGebra она уже есть, лучше и привычнее — цвет, толщина, стиль линии,
// прозрачность, всё на месте. Наше дело — не мешать ей.
const POINT_SIZE = 3;
const LINE_THICKNESS = 3;

// Дорисованное генератором красится, чтобы на плотном чертеже было видно, что
// именно добавилось. То, что ДОКАЗЫВАЕТСЯ, вдобавок пунктирное: оно не дано, а
// утверждается. У точки пунктира не бывает, поэтому она крупнее и полая.
const DRAWN_COLOR = [208, 0, 0];
const PROVE_POINT_SIZE = 6;
const PROVE_POINT_STYLE = 2;
const PROVE_LINE_STYLE = 2;

// ОФОРМИТЕЛЬ.
//
// Прежний держал набор уже оформленных имён и второй раз к имени не подходил.
// Из-за этого ломалось «назад»: undo НЕ ШЛЁТ НИ ОДНОГО СОБЫТИЯ (проверено —
// ни add, ни remove), GeoGebra просто перебирает конструкцию заново и
// освобождает имена. Освободившееся имя доставалось следующему объекту, тот
// считался уже оформленным, и на чертеже он выходил с умолчанием GeoGebra, то
// есть жирной пятёркой. Замерено на живом апплете: 3 → 5 → 3.
//
// Поэтому имена больше ни о чём не свидетельствуют. Оформляется КАЖДОЕ
// появление объекта, а оформленное человеком узнаётся по своему событию
// updateStyle — его GeoGebra шлёт как раз тогда, когда стиль меняют, и только
// тогда. Перекрасили объект руками — он таким и останется.
function makeStyler(applet) {
  const mine = new Set();          // объекты, которые оформили мы
  const byHand = new Set();        // и которые после этого правил человек
  let applying = false;

  const dress = (name, role) => {
    if (byHand.has(name) || !applet.exists?.(name)) return;
    mine.add(name);
    applying = true;
    try {
      const point = applet.getObjectType(name) === 'point';
      if (point) applet.setPointSize?.(name, role === 'prove' ? PROVE_POINT_SIZE : POINT_SIZE);
      else applet.setLineThickness?.(name, LINE_THICKNESS);
      if (role === 'prove') {
        if (point) applet.setPointStyle?.(name, PROVE_POINT_STYLE);
        else applet.setLineStyle?.(name, PROVE_LINE_STYLE);
      }
      if (role !== 'plain') applet.setColor?.(name, ...DRAWN_COLOR);
    } catch { /* оформление — украшение, из-за него терять объект незачем */ }
    applying = false;
  };

  // Стиль изменили не мы — значит это сделал человек, и больше мы к объекту не
  // подходим. Ровно этого и ждут от «поменять цвет уже нарисованного».
  try {
    applet.registerClientListener?.(e => {
      if (applying || e?.type !== 'updateStyle') return;
      if (e.target && mine.has(e.target)) { byHand.add(e.target); mine.delete(e.target); }
    });
  } catch { /* старая сборка апплета — обойдёмся без этого */ }

  return {
    add: name => dress(name, 'plain'),
    // Объект, который дорисовал генератор: 'draw' — участник, 'prove' — вывод.
    mark: (name, role) => { byHand.delete(name); dress(name, role); },
    // Объект убран с чертежа: забыть о нём, иначе имя вернётся «уже оформленным».
    forget: name => { mine.delete(name); byHand.delete(name); },
  };
}

// Оформитель нужен и генератору (дорисованное красится), поэтому живёт снаружи:
// создаётся, когда апплет готов.
let styler = null;

// ---- командная строка -----------------------------------------------------
const COMMANDS_KEY = 'complanator:commands';

function setupConsole() {
  const area = document.getElementById('commands');
  const report = document.getElementById('commands-report');
  area.value = localStorage.getItem(COMMANDS_KEY) ?? '';
  area.addEventListener('input', () => localStorage.setItem(COMMANDS_KEY, area.value));

  const show = results => {
    report.innerHTML = '';
    for (const item of results) {
      const div = document.createElement('div');
      div.className = item.error ? 'bad' : 'ok';
      const created = item.created?.map(c => c.name).join(', ');
      div.textContent = item.error
        ? `строка ${item.line}: ${item.error}`
        : `строка ${item.line}: ${created ? `построено ${created}` : 'ничего не построено'}`;
      // Не уложились во время — это не ошибка: ответ есть, он дорогой. Даём
      // кнопку, как и в таблице, вместо молчаливого зависания.
      if (item.compute) {
        div.className = 'pending-line';
        const button = document.createElement('button');
        button.type = 'button';
        button.className = 'canon compute';
        button.textContent = t('посчитать');
        button.title = `полный счёт: ${item.estimate}`;
        button.addEventListener('click', () => {
          button.disabled = true;
          button.textContent = t('считаю…');
          // Даём браузеру перерисоваться: счёт синхронный и надолго заберёт поток.
          setTimeout(() => {
            const started = Date.now();
            try {
              show(item.compute());
            } catch (e) {
              report.innerHTML = `<div class="bad">сбой: ${escapeHtml(e.message)}</div>`;
            }
            const note = document.createElement('div');
            note.className = 'note';
            note.textContent = `посчитано за ${Math.round((Date.now() - started) / 1000)} с`;
            report.appendChild(note);
          }, 30);
        });
        div.appendChild(document.createTextNode(' '));
        div.appendChild(button);
        const hint = document.createElement('span');
        hint.className = 'note';
        hint.textContent = item.estimate;
        div.appendChild(hint);
      }
      report.appendChild(div);
    }
  };

  const run = () => {
    if (!window.ggbApplet) { report.textContent = 'апплет ещё не загрузился'; return; }
    try {
      show(engine.runCommands(window.ggbApplet, area.value));
    } catch (e) {
      report.innerHTML = `<div class="bad">сбой: ${escapeHtml(e.message)}</div>`;
    }
  };

  document.getElementById('run-commands').addEventListener('click', run);
  area.addEventListener('keydown', e => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); run(); }
  });
  document.getElementById('commands-help').addEventListener('click', () => {
    report.innerHTML = COMMAND_HELP[engineKey];
  });
}

const COMMAND_HELP = {
  complex: `
<div><code>similar(X1..X6)</code> — X1X2X3 подобен X4X5X6, ориентация та же</div>
<div><code>angle(X1..X6)</code> — равенство направленных углов X1X2X3 и X4X5X6</div>
<div><code>angle(X1,X2,X3,D)</code> — угол X1X2X3 равен arg D, где D — направление
(задумано единичным). Вместе с <code>unity</code> это «угол равен 60°» одной
строкой: <code>angle(A,B,C,unity(6)^-1)</code></div>
<div><code>anglesum(+,X1,X2,X3, -,X4,X5,X6, …)</code> — знакопеременная сумма
направленных углов равна нулю; аргументы идут четвёрками «знак, три точки»</div>
<div><code>vectors(X1..X4)</code> — вектор X1X2 равен вектору X3X4</div>
<div><code>cocycl(X1..X4)</code> — четыре точки на одной окружности</div>
<div><code>paral(X1..X4)</code> — X1X2 параллельна X3X4</div>
<div><code>perpen(X1..X4)</code> — X1X2 перпендикулярна X3X4</div>
<div><code>harm(X1..X4)</code> — [X1X2, X3X4] = −1</div>
<div><code>collinear(X1,X2,X3)</code> — три точки на одной прямой</div>
<div><code>conconic(X1..X6)</code> — шесть точек на одной конике (одно вещественное условие, а не два: определитель тут веществен сам по себе)</div>
<div><code>krokhalyator(X1..X4)</code> — четвёрка ортоцентрическая (это сразу два условия)</div>
<div style="margin-top:6px"><b>Готовые построения</b> — не условия, а сразу точка:</div>
<div><code>incenter()</code> — инцентр ABC (через середины дуг: их движок строит сам)</div>
<div><code>isogonal(P)</code> — изогонально сопряжённая к P относительно ABC</div>
<div><code>krokhalyator(X1,X2,X3)</code> — четвёртая точка ортоцентрической четвёрки</div>
<div><code>rot90(P)</code> · <code>rot90(P,O)</code> — поворот на 90° (без центра — вокруг центра описанной)</div>
<div><code>rot60(P)</code> · <code>rot60(P,O)</code> — поворот на 60°</div>
<div><code>semiincircle()</code> — полувписанная окружность в угле A треугольника
ABC: касается AB, AC и описанной изнутри (аргументов не нужно)</div>
<div><code>segcircle(X1,X2,X3)</code> — окружности, вписанные в сегмент хорды
X2X3 и касающиеся дуги в X1 (их две — по одной в каждый сегмент)</div>
<div style="margin-top:6px">similar, vectors, harm и krokhalyator задают точку целиком;
остальные — вещественные условия, их нужно по два на точку.</div>
<div style="margin-top:6px">Аргумент — любое выражение, а не только имя точки:
<code>perpen(A, P, (Q+A)/3, X)</code>. Работают <code>+ − * /</code>, степень
<code>^</code> или <code>**</code>, скобки, <code>conj(...)</code> и
<code>unity(n)</code>.</div>
<div style="margin-top:6px"><code>unity(n)</code> — первообразный корень степени
n из единицы, то есть направление поворота на 360°/n. Поворот точки P вокруг C
на 60° пишется так: <code>buildpoint(C + (P-C)*unity(6))</code>. Берутся все n,
для которых правильный n-угольник строится циркулем и линейкой и нечётная часть
собрана из троек и пятёрок: 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 24, 30, 32, 40,
48, 60 и так далее. На 7, 9, 11 движок честно откажет — таких углов не бывает
вовсе; на 17 откажет тоже, но по другой причине (нужны периоды Гаусса).</div>
<div style="margin-top:6px">То же и в самой GeoGebra: <code>Rotate</code> теперь
принимает любой такой угол, а не только кратный 90°.</div>
<div style="margin-top:6px">Построения условий не накладывают и в одной строке
с ними не смешиваются:</div>
<div><code>buildpoint(выражение)</code> — точка прямо по формуле, можно с именем:
<code>buildpoint(M = (P+D+X)/3)</code>. Степень выражения не обязана быть первой:
<code>buildpoint(A^2)</code> и <code>buildpoint(1)</code> — законные точки описанной.</div>
<div><code>buildline(A, B, C)</code> — прямая по уравнению A·z + B·z̄ + C = 0</div>
<div><code>compass(A, B, C)</code> — циркуль: окружность с центром в C и радиусом
AB. Радикала не требует: окружность хранится квадратом радиуса, а |AB|²
рационально</div>
<div><code>radline(объект, объект)</code> — радикальная ось; объект это точка
(любое выражение) или окружность по её букве с панели. Ось двух точек —
срединный перпендикуляр, а точки и проходящей через неё окружности — касательная.</div>
<div><code>homothety(k1, k2)</code> — оба центра гомотетии двух окружностей,
внешний и внутренний. Окружности задаются буквами с панели. Радиус движку не
нужен: всё сводится к произведению радиусов, а оно рационально куда чаще, чем
каждый радиус по отдельности. Для описанной и окружности девяти точек получаются
ровно ортоцентр и центроид.</div>
<div><code>meet(объект, объект)</code> — пересечение двух объектов панели,
посчитанное ДВИЖКОМ, а не GeoGebra. Нужна там, где GeoGebra встаёт, вычисляя
пересечение сама: вкладка перестаёт отвечать, точка не появляется нигде. Эта
команда обходит её целиком; вместе с выключенным рисованием считает то, что
мышью просто не отметить.</div>
<div><code>tangent(P, k)</code> — касательные из точки P к окружности k. Точка —
любое выражение, окружность — буква с панели. Если P лежит на k, касательная
одна. Точки касания из произвольной внешней точки иррациональны, и тогда движок
честно отказывается, а не выдаёт неверное.</div>
<div style="margin-top:6px"><b>Коники.</b> Хранятся шестью коэффициентами
уравнения <code>A z² + B z z̄ + C z̄² + D z + E z̄ + F = 0</code> — пять степеней
свободы после множителя, ровно столько, сколько точек конику задаёт.</div>
<div><code>conic5(P1..P5)</code> — коника через пять точек</div>
<div><code>parabola(F, l)</code> — парабола по фокусу и директрисе; радикалов не
требует вовсе</div>
<div><code>conic(F1, F2, P)</code> — коника по двум фокусам и точке на ней. Через
них проходят ОБЕ кривые, эллипс и гипербола; строится эллипс. Полуось выражается
через корень из произведения расстояний до фокусов — когда он иррационален,
движок честно отказывается</div>
<div><code>centre(q)</code> — центр коники (у параболы его нет, и об этом
говорится прямо)</div>
<div><code>polar(P, q)</code> — поляра точки относительно коники ИЛИ окружности.
Поляра точки, лежащей на кривой, — касательная в ней, отдельной команды для
этого не нужно</div>
<div><code>commontangent(k1, k2)</code> — общие касательные двух окружностей и их
центры гомотетии. Отдельной механики тут нет: общая касательная проходит через
центр гомотетии — внешние через внешний, внутренние через внутренний, — поэтому
команда ставит оба центра и проводит касательные из каждого. Прямых бывает
меньше четырёх, и это ответ, а не сбой: у пересекающихся окружностей внутренних
касательных нет, у касающихся они сливаются в одну.</div>
`,
  bary: `
<div><b>Условия</b> — по системе на строку, неизвестная точка одна.</div>
<div><code>similar(X1..X6)</code> — X1X2X3 подобен X4X5X6, ориентация та же</div>
<div><code>angle(X1..X6)</code> — равенство направленных углов X1X2X3 и X4X5X6</div>
<div><code>vectors(X1..X4)</code> — вектор X1X2 равен вектору X3X4</div>
<div><code>cocycl(X1..X4)</code> — четыре точки на одной окружности</div>
<div><code>paral(X1..X4)</code> · <code>perpen(X1..X4)</code> — параллельность и перпендикулярность</div>
<div><code>harm(X1..X4)</code> — [X1X2, X3X4] = −1</div>
<div><code>collinear(X1,X2,X3)</code> — три точки на одной прямой</div>
<div><code>krokhalyator(X1..X4)</code> — четвёрка ортоцентрическая</div>
<div style="margin-top:6px">Неизвестная точка это (x : y : z), то есть ДВЕ степени
свободы. similar, vectors, harm и krokhalyator задают её целиком; остальные —
по одному условию, их нужно два. Каждое линейное условие — это прямая, на
которой лежит точка, поэтому «условий не хватает» значит буквально «осталась
целая прямая решений».</div>
<div style="margin-top:6px">Двух неизвестных сразу движок не берёт: в однородных
координатах условия по двум точкам перестают быть линейными. Стройте по очереди.</div>
<div style="margin-top:6px"><b>Построения</b> — с условиями в одной строке не смешиваются:</div>
<div><code>buildpoint(M = (P+D+X)/3)</code> — точка по формуле</div>
<div><code>buildline(l, m, n)</code> — прямая по уравнению l·x + m·y + n·z = 0</div>
<div><code>radline(объект, объект)</code> — радикальная ось (точка = окружность нулевого радиуса)</div>
<div><code>meet(объект, объект)</code> — пересечение, посчитанное движком</div>
<div><code>compass(X1, X2, X3)</code> — окружность с центром X3 и радиусом X1X2</div>
<div><code>tangent(окружность, точка)</code> — касательная в точке НА окружности</div>
<div><code>conic(X1..X5)</code> — коника по пяти точкам; если вышла окружность, так и покажет</div>
<div><code>homothety(k1, k2)</code> — центры гомотетии двух окружностей</div>
<div><code>equilateral(X1, X2)</code> — вершины равносторонних треугольников на
отрезке X1X2; их две, по одной с каждой стороны</div>
<div><code>etc(n)</code> — центр треугольника X(n) из таблицы; чего в ней нет,
про то будет сказано отдельно, и «требует √3» — не то же самое, что «не знаю».</div>
<div style="margin-top:6px"><b>Про √3.</b> Барицентрика не знает поворотов сама
по себе: в ней есть длины и площади, но нет углов. Поворот упирается в площадь
S, а она иррациональна. Движок присоединяет её одним корнем — для углов, кратных
60°, это ровно √3·S, — и дальше всё считается точно. Поэтому работают
<code>equilateral</code>, точки Торричелли X(13), X(14), изодинамические
(аполлониевы) X(15), X(16), точки Наполеона X(17), X(18), а в самой GeoGebra —
<code>Повернуть</code> на угол, кратный 60° или 90°.</div>
<div>30° и 45° потребовали бы двух корней сразу и пока не сделаны — об этом
будет сказано прямо, а не «не знаю».</div>
`,
};

// ---- строка выражений -----------------------------------------------------
const CALC_KEY = 'complanator:calc';

function setupCalculator() {
  const area = document.getElementById('calc');
  const report = document.getElementById('calc-report');
  area.value = localStorage.getItem(CALC_KEY) ?? '';
  area.addEventListener('input', () => localStorage.setItem(CALC_KEY, area.value));

  const show = results => {
    report.innerHTML = '';
    for (const item of results) {
      const div = document.createElement('div');
      if (item.error) {
        div.className = 'bad';
        div.textContent = `строка ${item.line}: ${item.error}`;
        report.appendChild(div);
        continue;
      }
      div.className = 'ok';
      div.innerHTML = item.target
        ? `<span class="name">${escapeHtml(item.target)}</span> =`
        : `<code>${escapeHtml(item.source)}</code> =`;
      const value = document.createElement('span');
      value.className = 'value';
      try {
        window.katex.render(item.tex, value, { throwOnError: false });
      } catch {
        value.textContent = item.text;
      }
      // приписка про вещественность — ради неё выражения обычно и считают
      if (item.nature) {
        const nature = document.createElement('span');
        nature.className = 'note nature';
        nature.textContent = item.nature;
        value.appendChild(nature);
      }
      div.appendChild(value);

      // «Домножить на общий знаменатель» — у Бариканатора. Дробь в ответе
      // законна (у вектора и у степени точки знаменатели бывают), но на бумаге
      // её обычно убирают, а насовсем убирать нельзя: тогда потерялся бы
      // масштаб вектора.
      if (item.cleared) {
        const button = document.createElement('button');
        button.type = 'button';
        button.className = 'canon';
        button.textContent = 'без дробей';
        button.title = 'домножить на общий знаменатель';
        let shown = false;
        button.addEventListener('click', () => {
          shown = !shown;
          button.textContent = shown ? 'как было' : 'без дробей';
          const out = shown ? item.cleared() : { text: item.text, tex: item.tex };
          value.innerHTML = '';
          try { window.katex.render(out.tex, value, { throwOnError: false }); }
          catch { value.textContent = out.text; }
        });
        div.appendChild(button);
      }

      // Полное разложение на неприводимые — ПО КНОПКЕ, а не само собой.
      // Автоматически печатается дешёвое и неполное: оно считается на каждый
      // запуск строки. Это же вправе думать секунды, потому что его попросили.
      if (item.factor) div.appendChild(factorButton(item, value));
      report.appendChild(div);
    }
  };

  const run = () => {
    try {
      show(engine.evaluate(area.value));
    } catch (e) {
      report.innerHTML = `<div class="bad">сбой: ${escapeHtml(e.message)}</div>`;
    }
  };

  let lastRows = null;
  const runAndKeep = () => {
    try {
      lastRows = engine.evaluate(area.value);
      show(lastRows);
    } catch (e) {
      report.innerHTML = `<div class="bad">сбой: ${escapeHtml(e.message)}</div>`;
    }
  };
  document.getElementById('run-calc').addEventListener('click', runAndKeep);
  wireLocus('calc', () => lastRows);
  area.addEventListener('keydown', e => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); runAndKeep(); }
  });
  document.getElementById('calc-help').addEventListener('click', () => {
    report.innerHTML = CALC_HELP[engineKey];
  });
}

// ГМТ по последней посчитанной строке.
//
// Уравнение — это условие на точки; объявим одну точку бегающей, остальные
// закреплёнными — и оно станет уравнением её геометрического места. Какая
// точка бегает, знает только пользователь: в «d·d̄ + a·d̄ + ā·d + b = 0» это
// может быть и d, и a. Поэтому букву спрашиваем, а не угадываем.
//
// Нарисованное попадает и в алгебру точек — уравнением, где бегающая буква
// названа z: так оно читается само по себе.
function wireLocus(kind, lastOf) {
  const button = document.getElementById(`${kind}-locus`);
  const field = document.getElementById(`${kind}-var`);
  const report = document.getElementById(`${kind === 'calc' ? 'calc' : 'conds'}-report`);
  if (!button) return;
  button.addEventListener('click', () => {
    const rows = lastOf();
    const applet = window.ggbApplet;
    const say = html => {
      const box = document.createElement('div');
      box.innerHTML = html;
      report.appendChild(box);
    };
    if (!rows?.length) {
      say('<div class="bad">сначала посчитайте строку — рисовать нечего</div>');
      return;
    }
    if (!applet) {
      say('<div class="bad">апплет ещё не загрузился</div>');
      return;
    }
    const varName = (field?.value || '').trim() || 'd';
    let any = false;
    for (const row of rows) {
      if (!row.value) continue;
      any = true;
      let out = null;
      try { out = engine.locus(applet, row.value, varName); }
      catch (e) { out = { error: e.message }; }
      if (out.error) {
        say(`<div class="bad">${escapeHtml(row.source)}: ${escapeHtml(out.error)}</div>`);
        continue;
      }
      say(`<div><b>${escapeHtml(out.name)}</b> — ${escapeHtml(out.kind)}`
        + (out.usable ? '' : ' <span class="bad">— выше второго порядка, строить по ней нельзя</span>')
        + (out.drawn ? '' : ' <span class="bad">(на чертёж не легла)</span>')
        + `<div class="cost">${escapeHtml(out.equation)}</div></div>`);
    }
    if (!any) say('<div class="bad">в этой строке нет уравнения — рисовать нечего</div>');
  });
}
const CALC_HELP = {
  complex: `
<div>операции: <code>+ - * /</code> и степень <code>^</code> (она же <code>**</code>,
как в Python), скобки, <code>conj(...)</code></div>
<div>имена точек чертежа берутся как есть: <code>H - A</code>, <code>(X-Y)/(X-Z)</code></div>
<div>переменные: <code>ratio = (X-Y)/(X-Z)</code> — имя не короче двух знаков,
иначе его не отличить от точки</div>
<div style="margin-top:6px"><code>distance(объект, объект)</code> — КВАДРАТ расстояния
(сам корень иррационален, а в проверках длина и так стоит в квадрате). Точка
задаётся выражением, прямая и окружность — своей буквой с панели:
<code>distance(A, B)</code>, <code>distance((P-2*A)*B/C, f)</code>. До окружности
считается степень точки: она просто подставляется в уравнение.</div>
<div style="margin-top:6px">умножение пишется явно: <code>2*A</code>, не <code>2A</code></div>
<div style="margin-top:6px">ответ раскладывается на множители; если он оказался
нулём — это подписывается. На вещественность автоматически не проверяем: это
дороже самого вычисления. Условие пишется явно, и ноль виден сразу:</div>
<div><code>r = (X-Y)/(X-Z)</code>, затем <code>r - conj(r)</code> —
ноль ⟺ X, Y, Z на одной прямой</div>
<div><code>q = (X-Y)/(Z-W)</code>, затем <code>q + conj(q)</code> —
ноль ⟺ XY ⟂ ZW</div>
<div><code>X*conj(X) - 1</code> — ноль ⟺ X на описанной окружности</div>
<div><code>distance(X,Y) - distance(Z,W)</code> — ноль ⟺ XY = ZW</div>
`,
  bary: `
<div>Значения ТИПИЗИРОВАНЫ, и от типа зависит смысл действия:</div>
<div><code>P - Q</code> между точками — вектор; <code>O1 - O2</code> между
окружностями — их радикальная ось</div>
<div><code>(A+B)/2</code> — середина, <code>(A+B+C)/3</code> — центроид: точка
внутри вычислений приводится к сумме координат единица, поэтому линейная
комбинация сама решает, точка она или вектор</div>
<div style="margin-top:6px"><code>line(P, Q)</code> — прямая через две точки</div>
<div><code>det(X1,X2,X3)</code> — определитель трёх точек (ноль ⟺ коллинеарны)
или трёх прямых (ноль ⟺ пересекаются в одной точке)</div>
<div><code>abs(P - Q)</code> — КВАДРАТ длины вектора</div>
<div><code>EFFT(u, v)</code> — ноль ⟺ векторы перпендикулярны</div>
<div><code>centre(k)</code> · <code>polar(k, P)</code> · <code>pow(k, P)</code> —
центр, поляра, степень точки</div>
<div style="margin-top:6px">умножение пишется явно: <code>2*A</code>, не <code>2A</code>;
степень — <code>^</code> или <code>**</code></div>
<div style="margin-top:6px">Кнопка «без дробей» домножает ответ на общий
знаменатель. Насовсем убирать дроби нельзя: у вектора это потеряло бы масштаб,
а с ним и длину.</div>
<div style="margin-top:6px">Готовые проверки:</div>
<div><code>det(X, Y, Z)</code> — ноль ⟺ X, Y, Z на одной прямой</div>
<div><code>EFFT(X-Y, Z-W)</code> — ноль ⟺ XY ⟂ ZW</div>
<div><code>pow(k, X)</code> — ноль ⟺ X на окружности k</div>
<div><code>abs(X-Y) - abs(Z-W)</code> — ноль ⟺ XY = ZW</div>
<div style="margin-top:6px">Кнопка «нарисовать ГМТ» читает посчитанное как
УСЛОВИЕ на одну точку: назовите её имя в поле «по точке», и Крополятор скажет,
какая это кривая, и нарисует её. Уравнение попадает в таблицу — в буквах
<code>u</code>, <code>v</code>, <code>w</code>, то есть в барицентрике самой
бегущей точки.</div>
`,
};

// ---- условие на точки -----------------------------------------------------
//
// Зеркало командной строки: там по условиям ищут точку, здесь по точкам ищут
// условие. Неизвестных нет, ответ — уравнение на вершины.
const CONDS_KEY = 'complanator:conds';

// Кнопка полного разложения: строка выражений и условие на точки. suffix —
// хвост формулы («= 0» у условия).
function factorButton(item, value, suffix = '') {
  const button = document.createElement('button');
  button.type = 'button';
  button.className = 'canon';
  button.textContent = 'разложить';
  button.title = 'полное разложение на неприводимые множители';
  button.addEventListener('click', () => {
    button.disabled = true;
    button.textContent = 'раскладываю…';
    // Даём браузеру перерисоваться: счёт синхронный.
    setTimeout(() => {
      let out = null;
      try {
        out = item.factor();
      } catch (e) {
        button.textContent = 'не уложилось';
        button.title = e.message;
        return;
      }
      if (!out) { button.textContent = 'дальше не раскладывается'; return; }
      try {
        window.katex.render(out.tex + (suffix ? ` ${suffix}` : ''), value, { throwOnError: false });
      } catch {
        value.textContent = out.text + (suffix ? ` ${suffix}` : '');
      }
      button.remove();
    }, 30);
  });
  return button;
}

function setupConditions() {
  const area = document.getElementById('conds');
  const report = document.getElementById('conds-report');
  area.value = localStorage.getItem(CONDS_KEY) ?? '';
  area.addEventListener('input', () => localStorage.setItem(CONDS_KEY, area.value));

  const show = results => {
    report.innerHTML = '';
    if (results.length === 0) return;
    for (const item of results) {
      const div = document.createElement('div');
      if (item.error) {
        div.className = 'bad';
        div.textContent = `строка ${item.line}: ${item.error}`;
        report.appendChild(div);
        continue;
      }
      div.className = 'ok';
      div.innerHTML = `<code>${escapeHtml(item.source)}</code> ⟺`;
      const value = document.createElement('span');
      value.className = 'value';
      if (item.identity) {
        // Тождество — это не уравнение на треугольник, и путать их нельзя:
        // «0 = 0» пользователь прочитал бы как «условие невыполнимо».
        value.textContent = 'выполняется всегда';
        value.classList.add('note');
      } else if (item.impossible) {
        // Ненулевая константа: «512 = 0» формально верно, но читается как
        // уравнение, у которого надо искать решение. Решений нет.
        value.textContent = 'не выполняется ни при каком треугольнике';
        value.classList.add('note');
      } else {
        try {
          window.katex.render(`${item.tex} = 0`, value, { throwOnError: false });
        } catch {
          value.textContent = `${item.text} = 0`;
        }
      }
      div.appendChild(value);
      if (item.factor) div.appendChild(factorButton(item, value, '= 0'));
      report.appendChild(div);
    }
  };

  const run = () => {
    try {
      show(engine.conditions(area.value));
    } catch (e) {
      report.innerHTML = `<div class="bad">сбой: ${escapeHtml(e.message)}</div>`;
    }
  };

  let lastRows = null;
  const runAndKeep = () => {
    try {
      lastRows = engine.conditions(area.value);
      show(lastRows);
    } catch (e) {
      report.innerHTML = `<div class="bad">сбой: ${escapeHtml(e.message)}</div>`;
    }
  };
  document.getElementById('run-conds').addEventListener('click', runAndKeep);
  wireLocus('conds', () => lastRows);
  area.addEventListener('keydown', e => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); runAndKeep(); }
  });
  document.getElementById('conds-help').addEventListener('click', () => {
    report.innerHTML = CONDS_HELP[engineKey];
  });
}

const CONDS_HELP = {
  complex: `
<div>Обратная задача к командной строке. Там пишут условие на НОВУЮ точку, и
движок её строит; здесь все точки уже есть, и движок отвечает, <b>при каких
вершинах</b> написанное выполняется.</div>
<div style="margin-top:6px">Команды те же: <code>collinear</code>, <code>perpen</code>,
<code>paral</code>, <code>angle</code>, <code>anglesum</code>, <code>cocycl</code>,
<code>similar</code>, <code>vectors</code>, <code>harm</code>,
<code>krokhalyator</code>. Аргумент — любое выражение, не только имя точки.</div>
<div style="margin-top:6px">Ответ раскладывается на множители, и это главное:
каждый множитель — отдельный случай, при котором условие выполняется.</div>
<div style="margin-top:6px"><code>perpen(A, M, B, C)</code>, где M — середина BC,
даёт <code>(b − c)(a² − bc) = 0</code>: либо B = C (вырождение), либо
<code>a² = bc</code> — а это в точности AB = AC, то есть равнобедренность.</div>
<div style="margin-top:6px">Если условие верно для любого треугольника, так и
пишется: «выполняется всегда».</div>
`,
  bary: `
<div>Обратная задача к командной строке. Там пишут условие на НОВУЮ точку, и
движок её строит; здесь все точки уже есть, и движок отвечает, <b>при каких
вершинах</b> написанное выполняется.</div>
<div style="margin-top:6px">Команды те же, кроме построений: <code>collinear</code>,
<code>perpen</code>, <code>paral</code>, <code>angle</code>, <code>cocycl</code>,
<code>similar</code>, <code>vectors</code>, <code>harm</code>,
<code>krokhalyator</code>. Аргумент — любое выражение, не только имя точки.</div>
<div style="margin-top:6px">Ответ раскладывается на множители, и это главное:
каждый множитель — отдельный случай, при котором условие выполняется.</div>
<div style="margin-top:6px"><code>perpen(A, M, B, C)</code>, где M — середина BC,
даёт <code>2(S_b − S_c) = 0</code>, то есть <code>b = c</code>: медиана
перпендикулярна стороне ровно у равнобедренного.</div>
<div><code>collinear(A, H, M)</code> даёт <code>4S_a(S_b − S_c) = 0</code> — либо
та же равнобедренность, либо <code>S_a = 0</code>, то есть прямой угол при A.</div>
<div style="margin-top:6px">«Выполняется всегда» и «не выполняется ни при каком
треугольнике» — разные ответы, и пишутся они словами: <code>0 = 0</code>
читалось бы как «условие невыполнимо».</div>
`,
};

// ---- рисовать ли найденное ------------------------------------------------
//
// Счёт у движка быстрый, а вот GeoGebra на длинных цепочках («касательная →
// точка на ней → прямая через неё → пересечение») встаёт уже сама, пересчитывая
// наши объекты на каждое обновление. Наш бюджет туда не дотягивается: там
// считает чужой код. Единственное, чем можно помочь, — не давать ей этой работы.
const DRAW_KEY = 'complanator:drawing';

function setupDrawToggle() {
  const button = document.getElementById('toggle-draw');
  let on = localStorage.getItem(DRAW_KEY) !== '0';

  const apply = () => {
    engine.setDrawing(on);
    button.textContent = on ? 'рисовать' : 'не рисовать';
    button.setAttribute('aria-pressed', String(!on));
  };
  button.addEventListener('click', () => {
    on = !on;
    localStorage.setItem(DRAW_KEY, on ? '1' : '0');
    apply();
  });
  apply();
}

let applyAlgebraView = () => {};

// TRIANGLECENTER ЖИВЁТ В ОТДЕЛЬНОМ МОДУЛЕ, И ОН ГРУЗИТСЯ ЛЕНИВО.
//
// Первый вызов после загрузки апплета не просто не срабатывает — он БРОСАЕТ
// «Discrete commands not loaded yet», и заодно запускает загрузку модуля.
// Дождаться её внутри одного синхронного прохода нельзя: догружает браузер, а
// он занят нашим же кодом. Поэтому пробуем заранее и с паузами.
//
// Без этого по кнопке «нарисовать» молча не строилась половина классических
// построений: ортоцентр, инцентр, центроид, прямая Обера — всё, что выражено
// через TriangleCenter, — а вместе с ними и то, что от них зависит.
const DISCRETE_WAITS = [0, 120, 350, 800, 1800];
let discreteReady = false;
async function ensureDiscrete(applet) {
  if (discreteReady) return true;
  if (typeof applet?.evalCommand !== 'function') return false;
  // Имя с приставкой cmpl — служебное: мост такие объекты пропускает.
  const probe = 'cmpldiscreteprobe';
  for (const wait of DISCRETE_WAITS) {
    if (wait) await new Promise(r => setTimeout(r, wait));
    try {
      applet.evalCommand(`${probe}=TriangleCenter((0,0),(1,0),(0,1),4)`);
      if (applet.exists(probe)) discreteReady = true;
    } catch { /* модуль ещё грузится — это и была наша заявка на загрузку */ }
    try { if (applet.exists(probe)) applet.deleteObject(probe); } catch { /* уже нет */ }
    if (discreteReady) return true;
  }
  return false;
}

function onAppletReady() {
  const ggbApplet = window.ggbApplet;
  statusEl.textContent = 'готов';
  // Свои окна с ошибками GeoGebra показывает поверх всего и требует нажатия.
  // Генератор перебирает несколько записей построения подряд — неудачная запись
  // для него дело обычное, а не повод останавливать пользователя. Ошибку мы и
  // так видим по тому, что объект не появился.
  try { ggbApplet.setErrorDialogsActive(false); } catch { /* старая сборка */ }
  styler = makeStyler(ggbApplet);
  ggbApplet.registerAddListener(name => {
    styler.add(name);
    engine.handleObject(ggbApplet, name);
  });
  ggbApplet.registerUpdateListener(name => engine.handleObject(ggbApplet, name));
  // апплет нужен и при удалении: если убрали образующую, построение
  // пересобирается целиком (буквы перераспределяются)
  ggbApplet.registerRemoveListener(name => {
    styler.forget(name);
    engine.remove(ggbApplet, name);
  });
  // Не дожидаемся: модулю нужно время, а нам сейчас ничего от него не нужно.
  // Важно только, чтобы к первому «нарисовать» он был уже здесь.
  ensureDiscrete(ggbApplet);
  applyAlgebraView();
  applyGrid();
  if (document.body.classList.contains('panel-off')) setTimeout(refit, 60);
}

const params = {
  appName: 'classic',
  // апплет растягивается под контейнер, а не под фиксированные 900×900 —
  // иначе перетаскивание разделителя ничего бы не меняло
  scaleContainerClass: 'stage',
  allowUpscale: true,
  showToolBar: true,
  // СТРОКА ВВОДА GeoGebra ВЫКЛЮЧЕНА ПО УМОЛЧАНИЮ.
  //
  // Она висит внизу полотна и съедает у чертежа полосу высотой с палец — а на
  // телефоне это заметная часть экрана. Своя командная строка у приложения
  // есть (панель справа), и вводить в неё удобнее. Кому нужна родная — она
  // приходит вместе с боковой панелью GeoGebra по той же кнопке.
  showAlgebraInput: false,
  showAlgebraView: false,
  showMenuBar: false,
  showResetIcon: true,
  enableRightClick: true,
  // Панель стиля (цвет, толщина, подпись) у выделенного объекта — на телефоне
  // правой кнопки нет, и без неё настроек объекта не достать вовсе.
  allowStyleBar: true,
  appletOnLoad: onAppletReady
};

window.addEventListener('load', () => {
  setupSplitter();
  setupFoldables();
  setupTabs();
  setupConsole();
  setupCalculator();
  setupConditions();
  setupEngineToggle();
  setupModeToggle();
  setupDrawToggle();
  applyAlgebraView = setupAlgebraToggle();
  // setupGenerator здесь НЕ ВЫЗЫВАЕТСЯ: панель строит список операций из OPS и
  // предикатов из PREDICATES, а их код платный и до подтверждения права не
  // скачан. Зовёт её openGenerator, когда право подтвердится.
  setupSave();
  setupHead();
  setupPanelToggle();
  setupGridToggle();
  setupLang();
  setupAccountModule();
  const applet = new window.GGBApplet(params, true);
  applet.inject('ggb-element');
});

// ---- полотно во весь экран и сетка ---------------------------------------
//
// На телефоне панель занимает половину экрана, а рисовать хочется на всём:
// кнопка в углу шапки прячет панель целиком и возвращает её. Сетка GeoGebra
// по умолчанию выключена — на чертеже она только мешает, — а включается
// кнопкой «сетка». Оба выбора запоминаются.
const PANEL_KEY = 'kropolyator:panelHidden', GRID_KEY = 'kropolyator:grid';

function setupPanelToggle() {
  const button = document.getElementById('toggle-panel');
  if (!button) return;
  let hidden = localStorage.getItem(PANEL_KEY) === '1';
  const apply = () => {
    document.body.classList.toggle('panel-off', hidden);
    button.setAttribute('aria-pressed', String(hidden));
    button.textContent = hidden ? '⤡' : '⤢';
    button.title = hidden ? 'вернуть панель' : 'спрятать панель — чертёж во весь экран';
    // Сначала размер апплета, потом толчок масштабу GeoGebra. В обратном
    // порядке масштаб считался по старому, высокому апплету и ужимал его вдвое.
    setTimeout(refit, 60);
  };
  button.addEventListener('click', () => {
    hidden = !hidden;
    localStorage.setItem(PANEL_KEY, hidden ? '1' : '0');
    apply();
  });
  apply();
}

// РАЗМЕР АППЛЕТА — ПО ПОЛОТНУ. Масштаб под контейнер (scaleContainerClass)
// подгоняет только ширину: на телефоне, когда панель спрятана, полотно
// вырастало в высоту, а апплет оставался прежним, и низ экрана пустовал.
function fitApplet() {
  const stage = document.querySelector('.stage');
  const head = stage?.querySelector('header');
  if (!stage || typeof window.ggbApplet?.setSize !== 'function') return;
  const w = Math.floor(stage.clientWidth), h = Math.floor(stage.clientHeight - (head?.offsetHeight ?? 0));
  if (w > 50 && h > 50) {
    try { window.ggbApplet.setSize(w, h); } catch { /* апплет ещё не поднялся */ }
  }
}

// Размер под полотно, затем пересчёт масштаба — уже по новому размеру.
function refit() {
  fitApplet();
  window.dispatchEvent(new Event('resize'));
}

let gridOn = false;
function applyGrid() {
  const button = document.getElementById('toggle-grid');
  button?.classList.toggle('on', gridOn);
  button?.setAttribute('aria-pressed', String(gridOn));
  try {
    window.ggbApplet?.setGridVisible?.(gridOn);
    // Оси — вместе с сеткой: на чертеже задачи они так же только мешают.
    window.ggbApplet?.setAxesVisible?.(gridOn, gridOn);
  } catch { /* апплет ещё не поднялся */ }
}

function setupGridToggle() {
  gridOn = localStorage.getItem(GRID_KEY) === '1';
  document.getElementById('toggle-grid')?.addEventListener('click', () => {
    gridOn = !gridOn;
    localStorage.setItem(GRID_KEY, gridOn ? '1' : '0');
    applyGrid();
  });
  applyGrid();
}

// ---- складная шапка ---------------------------------------------------------
//
// На телефоне чертежу достаётся меньше половины экрана, и шапка забирает у него
// ещё треть: заголовок, пояснение и четыре кнопки, которые нужны изредка.
// Поэтому на узком экране она свёрнута с самого начала — но именно свёрнута, а
// не убрана: полоска со стрелкой остаётся, и видно, что там что-то есть.
//
// Выбор запоминается. Один раз развернув шапку на телефоне, человек не должен
// разворачивать её снова после каждой перезагрузки.
const HEAD_KEY = 'kropolyator:headFolded';

function setupHead() {
  const button = document.getElementById('toggle-head');
  if (!button) return;
  const saved = localStorage.getItem(HEAD_KEY);
  // Узкий экран — свёрнута, широкий — раскрыта. Решает ширина, а не устройство:
  // окно браузера на столе тоже бывает в половину экрана.
  let folded = saved === null ? window.matchMedia('(max-width: 760px)').matches : saved === '1';

  const apply = () => {
    document.body.classList.toggle('head-folded', folded);
    button.setAttribute('aria-pressed', String(folded));
    button.title = folded ? 'развернуть шапку' : 'свернуть шапку, чтобы чертёж стал больше';
    // Апплет считает свой размер сам и о наших классах не знает: без толчка он
    // останется прежней высоты, и освобождённое место пропадёт впустую.
    setTimeout(refit, 60);
  };
  button.addEventListener('click', () => {
    folded = !folded;
    localStorage.setItem(HEAD_KEY, folded ? '1' : '0');
    apply();
  });
  apply();
}

// ---- выгрузка задачи и решения ----------------------------------------------
//
// Два действия и одна разница между ними: «сохранить задачу» отдаёт условие и
// чертёж, «получить решение» добавляет к ним протокол расчёта — координаты
// всех объектов и то, во что обратилось доказываемое.
//
// Модуль подгружается по требованию: выгрузка нужна изредка, а весит она
// вместе с разбором чертежа прилично.
function setupSave() {
  const claimField = document.getElementById('save-claim');
  const report = document.getElementById('save-report');
  const say = (text, bad) => {
    report.innerHTML = '';
    const div = document.createElement('div');
    div.className = bad ? 'bad' : 'ok';
    div.textContent = text;
    report.append(div);
  };

  // Координаты берём из таблицы: там ровно то, что человек видит на экране, —
  // пересчитывать их заново значило бы рисковать расхождением между файлом и
  // панелью.
  const tableRows = () => [...document.querySelectorAll('tbody tr')]
    .map(tr => ({
      name: tr.querySelector('.name')?.textContent.trim(),
      // Только исходная строка (см. dataset.plain в renderRow): текст ячейки
      // содержит ещё вёрстку формулы и подписи кнопок.
      value: tr.querySelector('.formula')?.dataset.plain?.trim(),
    }))
    .filter(r => r.name && r.value);

  const build = async (withProtocol) => {
    const claim = claimField.value.trim();
    try {
      const mod = await loadExport();
      let protocol = null;
      if (withProtocol) {
        // Утверждение проверяет тот же движок и тем же ходом, что и блок
        // «условие на точки»: другого способа у нас нет и заводить его незачем.
        const checks = claim ? engine.conditions(claim) : [];
        protocol = mod.protocolText({
          bridge: engine, applet: window.ggbApplet, rows: tableRows(), checks,
        });
      }
      const info = mod.saveProblem({
        bridge: engine, applet: window.ggbApplet,
        claim: claim || null, protocol,
        title: 'Задача',
      });
      say(`файл собран: строк условия ${info.lines}`
        + (info.image ? ', чертёж внутри' : ', без чертежа')
        + (withProtocol ? ', с протоколом расчёта' : ''));
    } catch (e) {
      say(`не вышло: ${e.message}`, true);
    }
  };

  document.getElementById('save-problem').addEventListener('click', () => build(false));
  document.getElementById('save-solution').addEventListener('click', () => build(true));
}

// ---- язык интерфейса -------------------------------------------------------
//
// Перевод живёт двумя путями: разметку переводит проход по пометкам data-t
// (см. applyLang), а то, что рисует код, — вызовы t. Здесь только склейка:
// применить сохранённый выбор и дать кнопку, чтобы его сменить.
//
// ПОКА ПЕРЕВЕДЕНЫ ТОЛЬКО ПОДПИСИ. Сообщения движка, пояснения и формулировки
// генератора остаются русскими — и это видно сразу, без обмана: непереведённое
// просто показывается по-русски, а не пропадает и не ломается.
function setupLang() {
  const button = document.getElementById('toggle-lang');
  const paint = () => {
    applyLang();
    if (button) button.textContent = lang() === 'ru' ? 'English' : 'Русский';
    // Подписи, которые ставит КОД, проход по разметке не трогает: заголовок
    // таблицы, название движка, его подсказка. Поэтому движок перерисовывается
    // целиком — applyEngine без перестройки это просто переписывание подписей.
    //
    // Вкладка «Алгебра» подтянется сама: её текст копируется с заголовка
    // панели наблюдателем (см. setupTabs).
    if (ENGINES[engineKey].bridge) applyEngine(false);
  };
  onLang(paint);

  // Неудача оставляет русский и не ломает ничего. Так бывает в сборке одним
  // файлом: словаря рядом с ней нет, и это не поломка, а её устройство.
  const fail = () => { statusEl.textContent = t('словарь не загрузился — остаёмся на русском'); };
  setLang(savedLang()).then(paint, () => { paint(); fail(); });

  if (button) {
    button.addEventListener('click', () => {
      setLang(lang() === 'ru' ? 'en' : 'ru').catch(fail);
    });
  }
}

// ---- учётные записи, права и чат -------------------------------------------
//
// Отдельным модулем и по требованию: приложение считает всё само и в сервере
// не нуждается. Если библиотека не загрузилась или сети нет — ничего не
// происходит, и работа идёт как прежде. Это не только про офлайн: версия
// «один файл» другого способа работать и не имеет.
function setupAccountModule() {
  // В сборке одним файлом модуля рядом нет: он и не нужен (см. метку в
  // build-standalone.mjs). Спрашиваем заранее, чтобы не оставлять в консоли
  // 404 — он выглядит поломкой, а поломки тут нет.
  if (window.__kropolyatorStandalone) {
    // Спрашивать некого, но ответ известен заранее: в сборке одним файлом есть
    // только Компланатор, а выгрузка доступна сразу — прав там нет вовсе.
    //
    // Идём тем же applyRights, а не трогаем узлы руками: иначе правила «что
    // видно» лежали бы в двух местах и разошлись бы на первой же правке. Здесь
    // же лечится и сохранённый выбор движка: кто переключился на Бариканатор
    // на сайте, тот в скачанном файле вернётся к Компланатору, а не упрётся в
    // таблицу, которую некому считать.
    applyRights({
      known: true, bary: false, gen: false, admin: false, signedIn: true,
      baryUntil: null, genUntil: null,
    });
    return;
  }
  import('./account.js')
    .then(mod => {
      // Модуль запоминается целиком: за платными движками ходить придётся
      // через него — токен сессии живёт там (см. paidModule выше).
      accountModule = mod;
      mod.onChange(applyRights);
      return mod.setupAccount();
    })
    .catch(() => { /* нет связи — значит без входа, чата и прав */ });
}

// ПАНЕЛЬ ГЕНЕРАТОРА СОБИРАЕТСЯ ТОЛЬКО ПОСЛЕ ТОГО, КАК ПОЛУЧЕН ЕГО КОД.
//
// Строится она из OPS и PREDICATES, а они приходят вместе с платным модулем.
// Поэтому порядок такой: право → код → сборка панели → показ. Открывать блок
// раньше нельзя: пустая панель читается как поломка.
// ФЛАГ СТАВИТСЯ ДО ПЕРВОГО ОЖИДАНИЯ, А НЕ ПОСЛЕ.
//
// Сперва он ставился в конце, после await loadGen(). Права приходят не один
// раз (сначала «ещё не знаем», потом ответ базы), applyRights зовёт эту
// функцию на каждый, и ДВА вызова успевали проскочить проверку раньше, чем
// любой из них доходил до флага. Панель строилась дважды.
//
// Видно это было двумя разными бедами, и связь между ними неочевидна:
// удваивался список предикатов — и переставала работать кнопка «условие».
// Вторая обиднее: она устроена переключателем, обработчиков оказывалось два,
// и одно нажатие выполняло оба — первый показывал условие, второй тут же его
// убирал. Снаружи это выглядит как мёртвая кнопка.
//
// Поэтому флаг взводится СИНХРОННО, первой же строкой: между проверкой и
// установкой не остаётся ни одного места, где поток мог бы уступить.
let generatorSet = false;
async function openGenerator() {
  if (generatorSet) return;
  generatorSet = true;
  const block = document.getElementById('gen-block');
  try {
    await loadGen();
  } catch (e) {
    // НЕУДАЧУ НАДО ПОКАЗАТЬ, А НЕ СПРЯТАТЬ.
    //
    // Сначала здесь стояло «оставить блок скрытым, причина — в строке
    // состояния». Так не годится по двум причинам. Строку состояния
    // перезаписывает апплет своим «готов», и причина исчезает. А человек, у
    // которого право ОТКРЫТО, видит вместо панели пустое место — и читает это
    // как «мне не продали», хотя продали, и дело в другом.
    //
    // Поэтому блок показывается и честно говорит, что случилось. Пустая
    // панель хуже отсутствующей, а панель с объяснением — лучше обеих.
    if (block) {
      block.hidden = false;
      const say = block.querySelector('summary');
      if (say) say.textContent = 'генератор теорем — не удалось загрузить';
      const note = document.createElement('div');
      note.className = 'gen-hint bad';
      note.textContent = `Право у вас есть, но модуль не пришёл: ${e.message}. `
        + 'Обновите страницу; если повторится — напишите владельцу сайта.';
      block.append(note);
    }
    // Флаг снимаем: попытка не удалась, и следующая смена прав вправе
    // попробовать снова. Иначе один сетевой сбой закрыл бы панель до
    // перезагрузки страницы.
    generatorSet = false;
    return;
  }
  setupGenerator();
  if (block) block.hidden = false;
}

// ЧТО ОТКРЫТО ЭТОМУ ЧЕЛОВЕКУ.
//
// ЗАКРЫТО — СОСТОЯНИЕ ПО УМОЛЧАНИЮ, и в разметке платные блоки стоят с hidden.
// Раньше было наоборот: пока права неизвестны, не ограничивалось ничего. Для
// прав, которые раздавал админ, это было удобно, а для платных — это дыра:
// «права неизвестны» на сайте значит всего лишь «библиотека ещё летит» или
// «её загрузку заблокировали», и блокировщик esm.sh открывал всё бесплатно.
// Порядок тот же, что у политик базы: забыть разрешить не страшно, забыть
// запретить страшно.
//
// known при этом НЕ ИСЧЕЗАЕТ, но значит только «ответ базы уже пришёл», и
// нужен в одном месте — там, где трогается сохранённый выбор движка.
function applyRights(r) {
  const engineButton = document.getElementById('toggle-engine');
  const genBlock = document.getElementById('gen-block');
  // Кнопка движка появляется по праву, не дожидаясь самого кода: право есть —
  // значит нажатие сработает, а скачивание займёт секунду и скажет об этом.
  if (engineButton) engineButton.hidden = !r.bary;
  // А вот панель генератора ЗАПРЕЩАЕТСЯ здесь, но ОТКРЫВАЕТСЯ не здесь: её
  // нечем наполнить, пока не пришёл код (см. openGenerator).
  if (genBlock && !r.gen) genBlock.hidden = true;
  if (r.gen) openGenerator();
  // ВЫГРУЗКА ТЕПЕРЬ В ТАРИФЕ ГЕНЕРАТОРА, а не просто «для вошедших», как было
  // раньше. Не по жадности: она пишет условие СЛОВАМИ, то есть тянет
  // statement.js, а с ним две трети генератора, которые от неё не отделяются
  // (см. шапку src/paid/export.js). В сборке одним файлом её не было никогда:
  // модуль подключается динамически, а сборщик таких не видит.
  const saveBlock = document.getElementById('save-block');
  if (saveBlock) saveBlock.hidden = !r.gen;
  // Право подтвердилось — возвращаем прошлый выбор человека.
  if (r.bary && wantedEngine === 'bary' && engineKey !== 'bary') chooseEngine('bary', true);
  // Бариканатор могли закрыть, пока он был включён, или кончился оплаченный
  // срок: возвращаем Компланатор, иначе человек остался бы перед таблицей,
  // которую ему больше не считают. Выбор при этом забывается — иначе он будет
  // проситься при каждой загрузке и каждый раз получать отказ.
  //
  // ТОЛЬКО ПО ИЗВЕСТНЫМ ПРАВАМ. Без known здесь оплативший Бариканатор терял
  // бы свой выбор при каждой загрузке: до ответа базы право закрыто, и выбор
  // успел бы перезаписаться в localStorage раньше, чем придёт разрешение.
  if (r.known && !r.bary) {
    wantedEngine = 'complex';
    try { localStorage.setItem(ENGINE_KEY, 'complex'); } catch { /* приватный режим */ }
    if (engineKey === 'bary') chooseEngine('complex', true);
  }
}

// ТЕКСТОВОЕ УСЛОВИЕ — НА ЯЗЫКЕ ИНТЕРФЕЙСА.
//
// Словарь подставляется ТОЛЬКО на время вызова и тут же снимается: остальная
// выдача (список найденного) остаётся русской, как и просил хозяин сайта.
// Englishем условие становится там, где его и просят текстом, — по кнопке
// «условие», в «условии без лишнего», в случайной задаче и в выгруженном
// файле.
//
// Если словарь ещё не приехал (платный модуль грузится отдельно), работает
// русский: отсутствие перевода не повод не показать условие вовсе.
const inUiLanguage = fn =>
  (lang() === 'en' && withVocabulary && EN ? withVocabulary(EN, fn) : fn());

// ---- генерирование теорем --------------------------------------------------

// Панель поверх той же конструкции, что уже разобрана мостом. Отдельного ввода
// у неё нет и не нужно: построение задаётся мышью в GeoGebra или командами
// выше, а здесь выбирают только ЧТО достраивать, СКОЛЬКО и что искать.
// ============================ генератор теорем ==============================

// Построения разложены по смыслу, а не по алфавиту: в панели их три десятка, и
// плоский список из них не читается.
const OP_GROUPS = [
  ['прямые', ['line', 'perp', 'par', 'perpbis', 'bisector', 'bisectorExt',
              'bisectorLL', 'bisectorLL2',
              'reflectLine', 'tangentAt', 'polar', 'radaxis']],
  ['точки', ['midpoint', 'foot', 'reflect', 'reflectPoint', 'center', 'invert',
             'rot90', 'rot90m', 'rot60', 'rot60m',
             'parallelogram', 'isotrapezoid', 'orthocenter']],
  ['окружности', ['circle3', 'circleCP', 'incircle', 'excircle',
                  'segcircle', 'semiincircle']],
  ['пересечения (идут в конце слоя)',
   ['meet', 'meetLC', 'meetLC2', 'otherLC', 'meetCC', 'meetCC2', 'otherCC',
    'tangent', 'tangent2']],
];

// КЛАССИЧЕСКИЕ ПОСТРОЕНИЯ — отдельным списком и с долями вместо галочек.
//
// Порядок групп — от того, что встречается в каждой второй задаче, к тому, что
// пореже. Полный перебор их не берёт никогда (см. gen/classic.js), поэтому
// лимита у них нет: есть доля жребиев случайного отбора.
const CLASSIC_GROUPS = [
  ['центры треугольника',
   ['incenter', 'excenter', 'centroid', 'circumcenter', 'ninepoint', 'lemoine',
    'gergonne', 'nagel', 'mittenpunkt', 'spieker', 'fermat']],
  ['Шалтай, Болтай и касания',
   ['humpty', 'dumpty', 'arcmid', 'arcmidA', 'touchpoint', 'extouchpoint',
    'tangentmeet', 'antipode']],
  ['сопряжения, прямые, окружность девяти точек',
   ['isogonal', 'isotomic', 'symmedian', 'eulerline', 'simson', 'steiner', 'ninecircle']],
  ['полный четырёхсторонник',
   ['miquel4', 'miquelLines', 'gaussline', 'aubertline']],
];

// Доли по умолчанию, в процентах. Двойка — тем, без кого олимпиадной
// планиметрии не бывает; единица — остальным. В сумме выходит около сорока:
// две пятых жребиев на классику, остальное обычным построениям.
const CLASSIC_FAVOURITES = new Set(['incenter', 'circumcenter', 'centroid', 'arcmid',
  'humpty', 'dumpty', 'isogonal', 'symmedian', 'miquel4', 'simson']);
const classicDefault = name => (CLASSIC_FAVOURITES.has(name) ? 2 : 1);

// Всё, что уходит в innerHTML, экранируется: имена объектов приходят с чертежа,
// а там пользователь волен назвать точку как угодно.
const escapeHtml = text =>
  String(text).replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));

const DEFAULT_OPS = { line: '', meet: '0' };

// Лимит, который подставляется при включении построения.
//
// У ПЕРЕСЕЧЕНИЯ ПРЯМЫХ это ноль, и это важнее, чем кажется: пустое поле значит
// «все пары», то есть квадрат от числа прямых. Именно отсюда берутся миллионы
// точек и часы поиска. Ноль значит «только точки схождения» — их примерно
// столько же, сколько прямых, и содержательны как раз они.
const SUGGESTED = { meet: '0', meetLC: '0', meetLC2: '0', meetCC: '0', meetCC2: '0' };
const DEFAULT_PREDS = ['collinear', 'concyclic', 'concurrent', 'parallel',
                       'perpendicular', 'length', 'angle', 'tangentLC', 'tangentCC'];

// Спрятать пояснения: каждый абзац-подсказку, стоящий сразу после строки
// настройки, сворачиваем и вешаем на строку знак вопроса.
function hideHints() {
  const block = document.getElementById('gen-block');
  if (!block) return;
  for (const row of block.querySelectorAll('label.gen-row, div.gen-cols')) {
    const hints = [];
    let next = row.nextElementSibling;
    while (next && next.classList.contains('gen-hint')) {
      hints.push(next);
      next = next.nextElementSibling;
    }
    if (!hints.length) continue;
    for (const h of hints) h.hidden = true;
    const ask = document.createElement('button');
    ask.type = 'button';
    ask.className = 'hint-toggle';
    ask.textContent = '?';
    ask.title = 'пояснение';
    ask.addEventListener('click', event => {
      event.preventDefault();
      const show = hints[0].hidden;
      for (const h of hints) h.hidden = !show;
      ask.classList.toggle('on', show);
    });
    row.appendChild(ask);
  }
}

function setupGenerator() {
  const opsBox = document.getElementById('gen-ops');
  const predsBox = document.getElementById('gen-preds');
  const report = document.getElementById('gen-report');
  const forecastBox = document.getElementById('gen-forecast');
  const essentialInput = document.getElementById('gen-essential');
  const roundsInput = document.getElementById('gen-rounds');
  const budgetInput = document.getElementById('gen-budget');
  const configsInput = document.getElementById('gen-configs');
  const secondsInput = document.getElementById('gen-seconds');
  const widthInput = document.getElementById('gen-width');
  const symmetryInput = document.getElementById('gen-symmetry');
  const stopper = document.getElementById('stop-gen');
  if (!opsBox) return;

  // Ключ хранилища подняли дважды. Сперва — из-за потолка в 60 000 объектов, при
  // котором поиск точек на одной окружности идёт сутками. Теперь — из-за
  // «объектов на слой»: сохранённые полтораста при потолке в пятнадцать тысяч
  // давали мир из трёхсот объектов за долю секунды. Забыть прежние настройки —
  // единственный способ, чтобы новое умолчание и правда стало умолчанием.
  const KEY = 'kropolyator.generator.v4';
  const drawn = [];
  const hidden = new Set();
  let last = null;

  // ---- элементы управления --------------------------------------------------

  for (const [title, names] of OP_GROUPS) {
    const head = document.createElement('div');
    head.className = 'gen-group';
    head.textContent = t(title);
    opsBox.appendChild(head);
    for (const name of names) {
      const op = OPS[name];
      if (!op) continue;
      const row = document.createElement('label');
      row.className = 'gen-op';
      row.title = op.note ? `${t(op.text)}. ${t(op.note)}` : t(op.text);
      row.innerHTML = `<input type="checkbox" data-op="${name}">`
        + `<input type="number" class="gen-limit" data-limit="${name}" min="0" step="1"`
        + ` placeholder="∞" title="${op.intersect
            ? 'сколько РЯДОВЫХ пересечений строить на слое; 0 — только точки схождения; пусто — сколько влезет'
            : 'сколько таких объектов строить на слое; пусто — сколько влезет в потолок'}">`
        + `<span>${escapeHtml(t(op.text))}</span>`;
      opsBox.appendChild(row);
    }
  }

  const classicBox = document.getElementById('gen-classic');
  const totalBox = document.getElementById('gen-classic-total');
  for (const [title, names] of CLASSIC_GROUPS) {
    if (!classicBox) break;
    const head = document.createElement('div');
    head.className = 'gen-group';
    head.textContent = t(title);
    classicBox.appendChild(head);
    for (const name of names) {
      const op = OPS[name];
      if (!op) continue;
      const row = document.createElement('label');
      row.className = 'gen-op gen-classic-row';
      row.title = op.note ? `${t(op.text)}. ${t(op.note)}` : t(op.text);
      row.innerHTML = `<input type="number" class="gen-share" data-classic="${name}"`
        + ` min="0" max="100" step="1" title="доля жребиев случайного отбора, %">`
        + `<span>${escapeHtml(t(op.text))}</span>`;
      classicBox.appendChild(row);
    }
  }

  for (const [name, p] of Object.entries(PREDICATES)) {
    const row = document.createElement('label');
    row.className = 'gen-pred';
    row.innerHTML = `<input type="checkbox" data-pred="${name}"><span>${escapeHtml(t(p.text))}</span>`;
    predsBox.appendChild(row);
  }

  const opBox = name => opsBox.querySelector(`[data-op="${name}"]`);
  const limitBox = name => opsBox.querySelector(`[data-limit="${name}"]`);

  // Что означает пустое «объектов на слой» — числом, а не словами: иначе
  // пользователь считает потолок в уме и ошибается ровно там, где это дорого.
  function showPerLayer() {
    const note = document.getElementById('gen-per-layer-note');
    if (!note) return;
    const field = document.getElementById('gen-per-layer');
    const layers = Number(roundsInput.value) || 2;
    const cap = Number(budgetInput.value) || 1500;
    const raw = (field?.value ?? '').trim();
    const per = raw === '' ? Math.max(1, Math.floor(cap / layers)) : Math.max(1, Number(raw) || 1);
    note.innerHTML = raw === ''
      ? `Первому слою достанется около <b>${nice(per)}</b> объектов, дальше — что`
        + ` осталось до потолка ${nice(cap)}. Недобор раннего слоя переходит следующим.`
      : `Мир выйдет примерно из <b>${nice(per * layers)}</b> объектов`
        + (per * layers < cap * 0.6
          ? ` — это заметно меньше потолка ${nice(cap)}: отведённое время не потратится.`
          : '.');
  }

  // Сумма долей — вслух. Складывать три десятка полей в уме пользователь не
  // обязан, а от суммы зависит, останется ли что-нибудь обычным построениям.
  function showClassicTotal() {
    if (!totalBox) return;
    const shares = classicShares();
    const sum = Object.values(shares).reduce((a, b) => a + b, 0);
    const n = Object.keys(shares).length;
    for (const box of classicBox.querySelectorAll('[data-classic]')) {
      box.classList.toggle('off', !(Number(box.value) > 0));
    }
    if (!n) {
      totalBox.innerHTML = 'Сейчас классика выключена целиком: все доли нулевые.';
      return;
    }
    totalBox.innerHTML = `Включено построений: <b>${n}</b>, в сумме <b>${sum}%</b> жребиев`
      + (sum >= 100
        ? ' — обычным построениям не останется ничего.'
        : ` — остальные <b>${100 - sum}%</b> делят между собой обычные построения.`);
  }

  function classicShares() {
    const out = {};
    for (const box of classicBox?.querySelectorAll('[data-classic]') ?? []) {
      const v = Math.max(0, Math.min(100, Number(box.value) || 0));
      if (v > 0) out[box.dataset.classic] = v;
    }
    return out;
  }

  // ОБЛАСТЬ ВЫБИРАЕТСЯ ГАЛОЧКОЙ, А НЕ ПИШЕТСЯ СТРОКОЙ.
  //
  // «Точка внутри окружности» может говорить о ПОСТРОЕННОМ объекте — о вписанной
  // окружности, о середине дуги, — а у такого имени на чертеже нет, и вписать его
  // в поле нельзя. Зато генератор сам читает с чертежа, что на нём верно, и
  // называет это человеческими словами; дело пользователя — отметить нужное.
  // Поэтому список появляется ПОСЛЕ прогона, а отмеченное идёт в следующий.
  // Наборы точек: по скольку точек в наборе и сколько наборов. Пустое поле у
  // числа наборов значит «столько, чтобы покрыть весь чертёж» — решает движок.
  function setOpts() {
    const num = id => {
      const raw = (document.getElementById(id)?.value ?? '').trim();
      if (raw === '') return null;
      const n = Number(raw);
      return Number.isFinite(n) && n > 0 ? Math.floor(n) : null;
    };
    const out = {};
    const mode = document.getElementById('gen-ineq-verify')?.value;
    if (mode && mode !== 'full') out.verify = mode;
    const over = num('gen-ineq-over');
    if (over && over !== 1) out.pool = { over };
    const per = num('gen-ineq-per-set');
    if (per) out.pointsPerSet = per;
    const many = num('gen-ineq-sets');
    if (many) out.sets = many;
    return out;
  }

  function pickedRegions() {
    const box = document.getElementById('gen-ineq-regions');
    if (!box) return [];
    return [...box.querySelectorAll('input[type=checkbox]:checked')].map(i => i.value);
  }

  function showRegions(drawn, used) {
    const box = document.getElementById('gen-ineq-regions');
    if (!box) return;
    // Отмеченное переживает прогон: снимать галочки за пользователя незачем.
    const on = new Set([...(used ?? []), ...pickedRegions()]);
    if (!drawn?.length) {
      box.innerHTML = 'На этом чертеже условий области не видно: ни остроугольных'
        + ' треугольников, ни точек внутри окружностей.';
      return;
    }
    box.innerHTML = '<b>Условия области, прочитанные с чертежа:</b>'
      + drawn.map(t => '<label class="gen-row"><span>' + escapeHtml(t) + '</span>'
        + `<input type="checkbox" value="${escapeHtml(t)}"${on.has(t) ? ' checked' : ''}></label>`)
        .join('');
  }

  // НАСТРОЙКА, КОТОРАЯ СЕЙЧАС НИЧЕГО НЕ ДЕЛАЕТ, ОБЯЗАНА ОБ ЭТОМ СКАЗАТЬ.
  //
  // Слои достраивания на величины не влияют: там счёт идёт от НАРИСОВАННЫХ
  // точек, а глубина достройки прямых и окружностей — своя настройка. Замерено:
  // один слой и три дают одни и те же находки, слово в слово, при мире в 13 и
  // 190 объектов. Пока выбраны только неравенства с тождествами, поле гасится и
  // говорит почему — иначе его крутят и ждут перемен.
  function syncIdle() {
    const row = document.getElementById('gen-rounds-row');
    const note = document.getElementById('gen-rounds-idle');
    if (!row || !note) return;
    const metric = !!(document.getElementById('gen-ineq-on')?.checked
      || document.getElementById('gen-ident-on')?.checked);
    const locus = !!document.getElementById('gen-locus-on')?.checked;
    const preds = [...(predsBox?.querySelectorAll('[data-pred]') ?? [])].some(b2 => b2.checked);
    // Два разных случая, и путать их нельзя. Если кроме величин ничего не
    // ищется — поле не работает вовсе, и его надо погасить. Если ищутся ещё и
    // равенства или ГМТ — поле работает, но НЕ НА ВЕЛИЧИНЫ, и об этом стоит
    // сказать, не отнимая настройку.
    const idle = metric && !locus && !preds;
    row.classList.toggle('idle', idle);
    const field = document.getElementById('gen-rounds');
    if (field) field.disabled = idle;
    note.hidden = !metric;
    if (idle) {
      note.textContent = 'сейчас это поле не работает: кроме величин ничего не ищется, а'
        + ' выражения строятся по НАРИСОВАННЫМ точкам. Глубину достройки прямых и'
        + ' окружностей задаёт отдельное поле в разделе неравенств.';
    } else if (metric) {
      note.textContent = 'на величины слои не влияют — там счёт идёт от нарисованных точек;'
        + ' глубину достройки прямых и окружностей задаёт отдельное поле в разделе'
        + ' неравенств. На поиск равенств и ГМТ слои работают как обычно.';
    }
  }

  function settings() {
    const selection = {};
    for (const box of opsBox.querySelectorAll('[data-op]')) {
      if (!box.checked) continue;
      const raw = limitBox(box.dataset.op).value.trim();
      selection[box.dataset.op] = raw === '' ? Infinity : Math.max(0, Number(raw) || 0);
    }
    return {
      selection,
      // Доли классических построений. В полном переборе их не будет в любом
      // случае — run.js берёт их только вместе со случайным отбором.
      classic: classicShares(),
      predicates: [...predsBox.querySelectorAll('[data-pred]')].filter(b => b.checked).map(b => b.dataset.pred),
      layers: Number(roundsInput.value) || 2,
      maxObjects: Number(budgetInput.value) || 1500,
      seconds: Number(secondsInput?.value) || 30,
      K: Number(configsInput.value) || 10,
      random: !!document.getElementById('gen-random')?.checked,
      // Пусто — значит «своя доля потолка»: считает closure.js, ему виднее,
      // сколько слоёв на самом деле пройдено.
      perLayer: Number(document.getElementById('gen-per-layer')?.value) || null,
      seed: Number(document.getElementById('gen-seed')?.value) || 1,
      keyFirst: !!document.getElementById('gen-keyfirst')?.checked,
      heavyOverGiven: !document.getElementById('gen-heavy-all')?.checked,
      essential: essentialInput.value.split(/[,\s]+/).map(s => s.trim()).filter(Boolean),
      // Условная теорема: пока галочка снята, посылки нет и всё идёт как раньше.
      hypothesis: document.getElementById('gen-hyp-on')?.checked
        ? (document.getElementById('gen-hyp')?.value ?? '') : '',
      hypothesisPoint: (document.getElementById('gen-hyp-point')?.value ?? '').trim() || null,
      inventHypothesis: !!(document.getElementById('gen-hyp-on')?.checked
        && document.getElementById('gen-hyp-invent')?.checked),
      // Задача на ГМТ: пустое поле значит «выбери подвижную сам».
      //
      // «P» — ездит как нарисована; «P: c» — по окружности c, чем бы она ни была
      // на чертеже; «P: плоскость» — по всей плоскости. Разделитель — запятая
      // или точка с запятой, но не пробел: после двоеточия стоит имя объекта.
      locus: document.getElementById('gen-locus-on')?.checked
        ? { moving: (document.getElementById('gen-locus-moving')?.value ?? '')
          .split(/[,;\n]+/).map(s => s.trim()).filter(Boolean)
          .map(part => {
            const m = /^(\S+)\s*[:=]\s*(.+)$/.exec(part);
            return m ? { name: m[1], along: m[2].trim() } : { name: part, along: null };
          }) }
        : null,
      // НЕРАВЕНСТВА. Условия области берутся отмеченными галочками, а список
      // галочек — с прошлого прогона: назвать построенный объект иначе нечем,
      // имени на чертеже у него нет (см. inequal.js).
      inequal: document.getElementById('gen-ineq-on')?.checked
        ? { regions: pickedRegions(), ...setOpts() } : null,
      // Тождества — своей галочкой: механизм общий, а спрашивают их порознь.
      identities: document.getElementById('gen-ident-on')?.checked
        ? { regions: pickedRegions(), ...setOpts() } : null,
      // «A, B, C» — взаимозаменяемы (все перестановки); «A -> B -> C» — цикл
      // (только повороты). Группы разделяются точкой с запятой.
      symmetryGroups: (symmetryInput?.value ?? '').split(';')
        .map(part => {
          const cyclic = part.includes('->');
          const names = part.split(cyclic ? '->' : ',')
            .map(x => x.trim()).filter(Boolean);
          return { names, cyclic };
        })
        .filter(g => g.names.length > 1),
    };
  }

  // Какой потолок мира влезает в отведённое время.
  //
  // Пользователь не обязан знать, что поиск точек на одной окружности растёт
  // кубом: он знает только, сколько готов ждать. Подбираем делением пополам —
  // оценка монотонна по потолку, так что это честный подбор, а не гадание.
  function fitCeiling(stub, s, seed = {}) {
    let lo = 20, hi = 200000;
    const costOf = cap => {
      const plan = estimate(stub, s.selection, s.layers, cap, s.heavyOverGiven, seed);
      const fac = n => { let t = 1; for (let i = 2; i <= n; i++) t *= i; return t; };
      // Симметрия закладывается: образы достраиваются, так что и на обрезанном
      // мире поиск пойдёт по орбитам. Цена достройки — треть лишних объектов,
      // она учтена ниже.
      const sym = s.symmetryGroups.length
        ? s.symmetryGroups.reduce((t, g) => t * (g.cyclic ? g.names.length : fac(g.names.length)), 1) : 1;
      const c = sym > 1
        ? { point: Math.round(plan.counts.point * 1.3), line: Math.round(plan.counts.line * 1.3),
            circle: Math.round(plan.counts.circle * 1.3) }
        : plan.counts;
      // Поиск пойдёт по орбитам только на большом мире — так же считает и
      // прогон (см. FULL_SEARCH_POINTS). Обещать орбиты там, где их не будет,
      // значит обещать время, которого не хватит.
      return ((plan.closureMs ?? 0) + searchCost(c, { predicates: s.predicates, K: s.K, symmetry: sym,
        symmetricOnly: sym > 1 && c.point > FULL_SEARCH_POINTS,
        keyPoints: s.keyFirst ? s.essential.length : 0 }).ms) / 1000;
    };
    if (costOf(hi) <= s.seconds) return hi;
    for (let i = 0; i < 24; i++) {
      const mid = Math.round((lo + hi) / 2);
      if (costOf(mid) <= s.seconds) lo = mid; else hi = mid;
    }
    return lo;
  }

  function restore() {
    let saved = null;
    try { saved = JSON.parse(localStorage.getItem(KEY) ?? 'null'); } catch { saved = null; }
    const ops = saved?.selection ?? DEFAULT_OPS;
    for (const box of opsBox.querySelectorAll('[data-op]')) {
      const has = Object.prototype.hasOwnProperty.call(ops, box.dataset.op);
      box.checked = has;
      limitBox(box.dataset.op).value = has ? (ops[box.dataset.op] ?? '') : '';
    }
    const classic = saved?.classic ?? null;
    for (const box of classicBox?.querySelectorAll('[data-classic]') ?? []) {
      const name = box.dataset.classic;
      box.value = classic ? (classic[name] ?? 0) : classicDefault(name);
    }
    const preds = saved?.predicates ?? DEFAULT_PREDS;
    for (const box of predsBox.querySelectorAll('[data-pred]')) box.checked = preds.includes(box.dataset.pred);
    if (saved?.layers) roundsInput.value = saved.layers;
    if (saved?.maxObjects) budgetInput.value = saved.maxObjects;
    if (saved?.K) configsInput.value = saved.K;
    for (const [id, key] of [['gen-per-layer', 'perLayer'], ['gen-seed', 'seed'],
                             ['gen-ineq-per-set', 'ineqPerSet'], ['gen-ineq-sets', 'ineqSets'],
                             ['gen-ineq-verify', 'ineqVerify'], ['gen-ineq-over', 'ineqOver']]) {
      const el = document.getElementById(id);
      if (el && saved?.[key]) el.value = saved[key];
    }
    for (const id of ['gen-random', 'gen-keyfirst', 'gen-heavy-all']) {
      const box = document.getElementById(id);
      if (box && saved?.[id] !== undefined) box.checked = !!saved[id];
    }
    if (saved?.seconds && secondsInput) secondsInput.value = saved.seconds;
    if (saved?.symmetry && symmetryInput) symmetryInput.value = saved.symmetry;
    if (saved?.essential) essentialInput.value = saved.essential.join(', ');
    showClassicTotal();
    showPerLayer();
  }

  function remember() {
    const s = settings();
    const selection = {};
    for (const [k, v] of Object.entries(s.selection)) selection[k] = Number.isFinite(v) ? v : '';
    const flags = {};
    for (const id of ['gen-random', 'gen-keyfirst', 'gen-heavy-all'])
      flags[id] = !!document.getElementById(id)?.checked;
    // Наборы точек хранятся как есть, а не внутри inequal: панель может быть
    // выключена, а поля пользователь уже настроил — терять их незачем.
    const ineqPerSet = document.getElementById('gen-ineq-per-set')?.value ?? '';
    const ineqSets = document.getElementById('gen-ineq-sets')?.value ?? '';
    const ineqVerify = document.getElementById('gen-ineq-verify')?.value ?? '';
    const ineqOver = document.getElementById('gen-ineq-over')?.value ?? '';
    try { localStorage.setItem(KEY, JSON.stringify({ ...s, ...flags, selection,
      ineqPerSet, ineqSets, ineqVerify, ineqOver,
      symmetry: symmetryInput?.value ?? '' })); }
    catch { /* приватный режим */ }
  }

  // ---- разведка первого слоя ------------------------------------------------
  //
  // Первый слой не оценивается, а СТРОИТСЯ по-настоящему. Оценка не умеет
  // предсказывать склейку — перпендикуляры из разных точек к одной прямой
  // совпадают, прямая через две точки часто уже есть, — а склейки много, и она
  // переворачивает состав мира. Обещалось 15 000 прямых и 256 точек, выходило
  // 517 прямых и 14 483 точки; поиск квадратичен по прямым и КУБИЧЕН по точкам,
  // так что вместе с составом врала и вся цена.
  //
  // Разведка стоит доли секунды, а второй слой зависит от первого целиком.
  let probed = null;

  const drawingKey = () => [engine.pointExpr, engine.lineDefs, engine.circleDefs]
    .map(m => [...(m?.keys() ?? [])].join(',')).join('|');

  // Партнёры по объявленной симметрии видны генератору наравне с ключевыми
  // (см. run.js). Разведка обязана строить ТОТ ЖЕ мир, что и прогон: лишняя
  // данная точка — это разница между четырьмя тройками и десятью, и прогноз
  // без неё обещает вчетверо меньше работы, чем будет.
  const symPartners = s => [...new Set((s.symmetryGroups ?? []).flatMap(g => g?.names ?? []))]
    .filter(n => n && !s.essential.includes(n));

  async function probeLayer(s) {
    const also = symPartners(s);
    const key = JSON.stringify([drawingKey(), s.essential, also, s.selection, s.K, s.heavyOverGiven]);
    if (probed?.key === key) return probed;
    let out = { key, ok: false };
    if (engine === ENGINES.complex.bridge) {
      try {
        const built = worldFromBridge(engine, {
          applet: window.ggbApplet ?? null, essential: s.essential, alsoVisible: also,
          K: s.K, seed: s.seed,
        });
        if (built.world) {
          const res = await probe(built.world, s.selection,
            { maxObjects: PROBE_CAP, heavyOverGiven: s.heavyOverGiven, layers: s.layers,
              msBudget: 2500 });
          out = { key, ...res };
        }
      } catch { out = { key, ok: false }; }
    }
    probed = out;
    return out;
  }

  // ---- предварительная оценка ----------------------------------------------
  //
  // Считается ДО прогона и по тем же формулам, что и сам перебор. Пользователь
  // должен видеть, чем себя ограничивать, а не узнавать это по зависшей вкладке.
  // Асинхронный: он строит первый слой по-настоящему. Зовут его через
  // scheduleForecast — с задержкой, чтобы разведка не запускалась на каждую
  // нажатую цифру.
  async function forecast() {
    const s = settings();
    const counts = { point: 0, line: 0, circle: 0 };
    const keep = new Set(s.essential);
    const take = (map, kind) => {
      for (const name of map?.keys() ?? []) if (!keep.size || keep.has(name)) counts[kind]++;
    };
    take(engine.pointExpr, 'point');
    take(engine.lineDefs, 'line');
    take(engine.circleDefs, 'circle');

    if (!counts.point && !counts.line && !counts.circle) {
      forecastBox.innerHTML = '<p class="gen-hint">чертёж пуст — строить не из чего</p>';
      return;
    }
    const stub = { count: k => counts[['point', 'line', 'circle'][k]] };
    const pr = await probeLayer(s);
    const seed = pr.ok
      ? { base: pr.counts, given: pr.given, from: (pr.layers ?? 1) + 1,
          seedRows: pr.rows, doneMs: pr.ms, steps: pr.steps, start: pr.start }
      : {};
    let plan;
    try { plan = estimate(stub, s.selection, s.layers, s.maxObjects, s.heavyOverGiven, seed); }
    catch { forecastBox.innerHTML = ''; return; }
    if (!plan.rows.length) { forecastBox.innerHTML = '<p class="gen-hint">не выбрано ни одного построения</p>'; return; }

    // Главное здесь — не размер мира, а цена ПОИСКА. Мир растёт линейно, а поиск
    // точек на одной окружности — кубом от числа точек, и именно он решает,
    // будет прогон секундой или сутками. Поэтому оценка времени идёт первой
    // строкой и крупно, а таблица построений спрятана под сводку.
    // Порядок группы симметрий: сколько перестановок допускают объявленные
    // равноправными объекты.
    //
    // Настоящая группа может оказаться МЕНЬШЕ, и не только потому, что чертёж
    // перестановку не допускает. Симметрия живёт на всём мире сразу, а потолок
    // обрывает мир посреди перебора — у объекта, построенного до обрыва, образ
    // может оказаться после него. Обрезанный мир несимметричен, и поиск по
    // орбитам на нём не запускается. Поэтому там, где потолок режет, крупно
    // пишется цена БЕЗ симметрии — она сбудется наверняка, — а выигрыш от
    // симметрии отдельной строкой как возможность.
    const fact = n => { let t = 1; for (let i = 2; i <= n; i++) t *= i; return t; };
    const symmetry = s.symmetryGroups.length
      ? s.symmetryGroups.reduce((t, g) => t * (g.cyclic ? g.names.length : fact(g.names.length)), 1) : 1;
    const opts = { predicates: s.predicates, K: s.K, symmetry,
      symmetricOnly: symmetry > 1 && plan.counts.point > FULL_SEARCH_POINTS,
      keyPoints: s.keyFirst ? s.essential.length : 0 };
    const plainOpts = { ...opts, symmetry: 1, symmetricOnly: false };
    // Объявленная симметрия ДОСТРАИВАЕТ недостающие образы, и мир от этого
    // растёт: по замерам от пяти до полусотни процентов. Берём треть — с
    // запасом в ту сторону, где ошибиться не жалко.
    const grown = symmetry > 1
      ? { point: Math.round(plan.counts.point * 1.3),
          line: Math.round(plan.counts.line * 1.3),
          circle: Math.round(plan.counts.circle * 1.3) }
      : plan.counts;
    const withSym = searchCost(grown, opts);
    const noSym = searchCost(plan.counts, plainOpts);
    // Симметрия теперь срабатывает и на обрезанном мире — образы достраиваются.
    // Не сработает она только если ЧЕРТЁЖ такой перестановки не допускает, а это
    // прогноз проверить не может: он про числа, а не про построение. Поэтому
    // цена без симметрии всё равно показывается — второй строкой.
    const risky = symmetry > 1;
    const cost = withSym;
    const probeSize = pr.ok ? pr.counts.point + pr.counts.line + pr.counts.circle : 0;
    const closureSecs = (plan.closureMs ?? 0) / 1000;
    const secs = cost.ms / 1000 + closureSecs;
    const time = secs < 1 ? 'меньше секунды'
      : secs < 90 ? `около ${Math.round(secs)} с`
      : secs < 5400 ? `около ${Math.round(secs / 60)} мин`
      : `около ${Math.round(secs / 3600)} ч — столько ждать не стоит`;
    const alarm = secs > 120 ? ' warn' : '';
    const plainSecs = noSym.ms / 1000 + closureSecs;
    const plainTime = plainSecs < 1 ? 'меньше секунды'
      : plainSecs < 90 ? `около ${Math.round(plainSecs)} с`
      : plainSecs < 5400 ? `около ${Math.round(plainSecs / 60)} мин`
      : `около ${Math.round(plainSecs / 3600)} ч`;

    // ПОЛНОЕ замыкание — то, при котором на этом числе слоёв найдётся ВСЁ.
    // Это и есть ответ на вопрос «какой потолок ставить»: меньше — часть теорем
    // не найдётся, больше — бессмысленно, строить всё равно нечего.
    const full = estimate(stub, s.selection, s.layers, Infinity, s.heavyOverGiven, seed);
    const fullCost = searchCost(full.counts, opts);
    const fullSecs = fullCost.ms / 1000;
    const fullTime = fullSecs < 1 ? 'меньше секунды'
      : fullSecs < 90 ? `${Math.round(fullSecs)} с`
      : fullSecs < 5400 ? `${Math.round(fullSecs / 60)} мин`
      : fullSecs < 86400 * 3 ? `${Math.round(fullSecs / 3600)} ч`
      : `${Math.round(fullSecs / 86400)} сут`;

    const fit = fitCeiling(stub, s, seed);

    // «Сколько надо, чтобы нашлось всё» имеет смысл, только пока это обозримое
    // число. Со всеми построениями на двух слоях полное замыкание уходит в
    // 10⁵¹ объектов — печатать такое незачем, надо СКАЗАТЬ, что так не бывает,
    // и показать, какие построения взрывают перебор. Это и есть ответ на «какие
    // построения не имеют смысла»: те, у которых наборов на порядки больше, чем
    // весь мир, — они съедают потолок и не дают дойти до остальных.
    const REACHABLE = 200_000;
    let fullLine;
    if (full.total <= REACHABLE) {
      fullLine = `<p class="gen-stat">чтобы на ${s.layers} ${s.layers === 1 ? 'слое' : 'слоях'}`
        + ` нашлось ВСЁ, потолок должен быть <b>${nice(Math.round(full.total))}</b>`
        + ` — тогда поиск с отсевом займёт ${fullTime}</p>`;
    } else {
      const worst = plan.rows.filter(r => r.layer === s.layers)
        .sort((a, b) => b.combos - a.combos).slice(0, 3)
        .map(r => `${escapeHtml(r.text)} (${nice(Math.round(r.combos))})`).join(', ');
      fullLine = '<p class="gen-stat warn">полное замыкание на этом наборе построений'
        + ' необозримо: обыскать его целиком не сможет никакой генератор.'
        + ' Будет найдено только то, что влезло в потолок.</p>'
        + `<p class="gen-hint">дороже всего на последнем слое: ${worst}.`
        + ' Уберите лишние построения, поставьте им лимиты или отметьте ключевые'
        + ' объекты — тогда потолок потратится на то, что вам нужно.</p>';
    }

    // Строки разведанного слоя помечены: там не оценка, а замер.
    const rows = plan.rows.map(r =>
      `<tr${r.real ? ' class="real"' : ''}><td>${r.layer}${r.real ? ' ✓' : ''}</td>`
      + `<td>${escapeHtml(r.text)}</td>`
      + `<td class="num">${nice(Math.round(r.combos))}</td>`
      + `<td class="num">${nice(Math.round(r.made))}</td></tr>`);

    const perStage = Object.entries(cost.per).filter(([, v]) => v > 0)
      .sort((a, b) => b[1] - a[1])
      .map(([n, v]) => `${escapeHtml(PREDICATES[n]?.text ?? n)} — ${nice(Math.round(cost.sets[n]))} наборов,`
        + ` ${(v * 1e-9).toFixed(v * 1e-9 < 1 ? 2 : 0)} с`).join('; ');

    forecastBox.innerHTML =
      `<p class="gen-stat${alarm}">мир ≈ <b>${nice(Math.round(plan.total))}</b>`
      + ` ${plural(plan.total, 'объект', 'объекта', 'объектов')}`
      + ` (${nice(plan.counts.point)} точек, ${nice(plan.counts.line)} прямых)`
      + (pr.ok
        ? `. Первый слой построен на самом деле: в нём `
          + (pr.full ? 'не меньше ' : '')
          + `<b>${nice(probeSize)}</b>`
          + ` ${plural(probeSize, 'объект', 'объекта', 'объектов')}`
          + (probeSize > s.maxObjects
            ? ', и потолка на него не хватает — до второго слоя дело не дойдёт'
            : '')
        : '')
      + `. Замыкание — `
      + (closureSecs < 1 ? 'меньше секунды' : `около ${Math.round(closureSecs)} с`)
      + `, поиск с первичным отсевом — <b>${time}</b>`
      + (plan.capped ? `; упирается в потолок ${nice(s.maxObjects)}` : '')
      + '</p>'
      + (risky
        ? '<p class="gen-hint">время посчитано по объявленной симметрии: поиск идёт'
          + ' по орбитам, а недостающие образы генератор достраивает сам (мир от'
          + ' этого вырастает примерно на треть, это уже учтено). Если ЧЕРТЁЖ такой'
          + ` перестановки не допускает, симметрии не будет, и поиск с отсевом займёт ${plainTime}.</p>`
        : '')
      + fullLine
      + `<p class="gen-stat">в ${s.seconds} с укладывается потолок <b>${nice(fit)}</b>`
      + (fit >= full.total ? ' — этого хватает на всё' : '')
      + ` <button type="button" class="chip" id="take-ceiling">поставить</button></p>`
      + '<details class="gen-ceiling"><summary>подробно</summary>'
      + `<p class="gen-hint">по стадиям: ${perStage || 'ничего не выбрано'}.`
      + ` Конфигураций ${s.K}: раскладка идёт по одной из них, поэтому от их числа`
      + ' время почти не зависит — зависит подтверждение, а его мало.'
      + ' Если условие симметрично (треугольник — шесть перестановок), перебор'
      + ' сокращается ещё в разы: генератор находит симметрии сам и пользуется ими.</p>'
      + '<table class="gen-ceiling-table"><tr><th>слой</th><th>построение</th>'
      + '<th>наборов</th><th>построит ≤</th></tr>' + rows.join('') + '</table>'
      + `<p class="gen-hint">Галочкой отмечен слой, который РАЗВЕДАН: он построен`
      + ' по-настоящему, и там стоит не оценка, а замер. Остальные слои считаются'
      + ' от него, и в них «построит ≤» — верхняя граница: сколько объектов'
      + ' склеится, заранее не знает никто.</p></details>';

    forecastBox.querySelector('#take-ceiling')?.addEventListener('click', () => {
      budgetInput.value = fit;
      remember();
      forecast();
    });
  }

  // Разведка строит слой по-настоящему, поэтому прогноз пересчитывается не на
  // каждое нажатие, а через паузу после последнего.
  let forecastTimer = null;
  const scheduleForecast = () => {
    clearTimeout(forecastTimer);
    forecastTimer = setTimeout(() => { forecast(); }, 250);
  };

  for (const id of ['gen-ineq-on', 'gen-ident-on', 'gen-locus-on']) {
    document.getElementById(id)?.addEventListener('change', syncIdle);
  }
  predsBox?.addEventListener('change', syncIdle);
  syncIdle();

  for (const id of ['gen-random', 'gen-keyfirst', 'gen-per-layer', 'gen-seed',
                    'gen-ineq-per-set', 'gen-ineq-sets', 'gen-ineq-verify', 'gen-ineq-over']) {
    const el = document.getElementById(id);
    el?.addEventListener('change', () => { remember(); scheduleForecast(); });
  }

  // Включили построение — подставляем осмысленный лимит, если поле пустое.
  // Что означает ноль у пересечения, надо видеть, а не догадываться: молчащий
  // ноль в поле пользователь читает как «не строить», а он значит «только
  // точки схождения» — и мир от этого выходит совсем другой.
  function markLimits() {
    for (const box of opsBox.querySelectorAll('[data-op]')) {
      const op = OPS[box.dataset.op];
      const row = box.closest('label');
      if (!op?.intersect || !row) continue;
      let tag = row.querySelector('.gen-onlyjoin');
      const zero = box.checked && limitBox(box.dataset.op)?.value.trim() === '0';
      if (zero && !tag) {
        tag = document.createElement('span');
        tag.className = 'gen-onlyjoin';
        tag.textContent = ' только схождения';
        row.appendChild(tag);
      } else if (!zero && tag) tag.remove();
    }
  }

  opsBox.addEventListener('change', event => {
    const box = event.target.closest('[data-op]');
    if (box?.checked) {
      const field = limitBox(box.dataset.op);
      if (field && field.value === '' && SUGGESTED[box.dataset.op] !== undefined)
        field.value = SUGGESTED[box.dataset.op];
    }
    markLimits();
  });
  opsBox.addEventListener('input', markLimits);

  // Доли классических построений на прогноз не влияют: прогноз считает полный
  // перебор, а классика живёт только в случайном отборе. Поэтому — только
  // запомнить и пересчитать сумму.
  classicBox?.addEventListener('input', () => { showClassicTotal(); remember(); });

  for (const el of [opsBox, predsBox, roundsInput, budgetInput, configsInput, essentialInput,
                    secondsInput, symmetryInput].filter(Boolean))
    el.addEventListener('input', () => { remember(); showPerLayer(); scheduleForecast(); });
  document.getElementById('gen-per-layer')?.addEventListener('input',
    () => { showPerLayer(); remember(); });

  // ---- вывод ----------------------------------------------------------------

  // Поле условия показывается только когда оно нужно.
  for (const [flag, panel] of [['gen-hyp-on', 'gen-hyp-box'],
                               ['gen-locus-on', 'gen-locus-box'],
                               ['gen-ineq-on', 'gen-ineq-box'],
                               ['gen-ident-on', 'gen-ident-box']]) {
    const on = document.getElementById(flag);
    const box = document.getElementById(panel);
    const sync = () => { if (box) box.hidden = !on?.checked; };
    on?.addEventListener('change', sync);
    sync();
  }

  const say = html => { report.innerHTML = html; };

  function renderResult(res, ms) {
    if (res.failed) { say(`<p class="warn">не получилось: ${escapeHtml(res.failed)}</p>`); return; }
    last = res;
    const parts = [];

    // ЧТО НАШЛИ — ВСЕГДА, КАК СЧИТАЛИ — ПОД ВОПРОСИКОМ.
    //
    // Отчёт разросся: размер мира, прогноз, время по стадиям, разбивка отсева.
    // Всё это нужно ровно тогда, когда результат озадачил, — а в остальное
    // время загораживает саму выдачу. Поэтому счёт уезжает в свёрнутый блок, а
    // снаружи остаётся то, что меняет доверие к ответу: предупреждения, обрывы
    // и сам список.
    const detail = [];

    if (res.problems?.length)
      parts.push(`<p class="gen-hint">чего генератор не увидел: ${res.problems.map(escapeHtml).join('; ')}</p>`);

    // ЖЁСТКОЕ СЕМЕЙСТВО — крупно и первым делом: под ним вся выдача ничего не
    // стоит, и прочесть её как теоремы — прямая ошибка.
    if (res.hypothesis?.rigid)
      parts.push('<p class="warn">условий столько же, сколько у чертежа свободы: фигура'
        + ' остаётся ОДНА с точностью до подобия. «Верно во всех конфигурациях» на ней'
        + ' ничего не значит — конфигурация по сути одна, и найденное верно лишь для этой'
        + ' фигуры, а не вообще. Снимите одно из условий.</p>');

    // ЧТО ЗА ОБЛАСТЬ И ЧЕГО СТОИЛ ПОИСК — сверху: без области половина
    // неравенств читается неверно.
    if (res.inequal) {
      showRegions(res.inequal.drawn, res.inequal.used);
      const kinds = res.inequal.kinds ?? ['bound'];
      const what = kinds.length === 2 ? 'неравенства и тождества'
        : kinds[0] === 'identity' ? 'тождества' : 'геометрические неравенства';
      parts.push(`<p class="gen-stat">${what}`
        + (res.inequal.used.length
          ? ` при <b>${escapeHtml(res.inequal.used.join(' и '))}</b>`
          : ' (без условий на область)')
        + `; выражений ${nice(res.inequal.forms)}, пар ${nice(res.inequal.pairs)},`
        + (res.inequal.sets > 1
          ? ` наборов точек ${nice(res.inequal.sets)} по ${nice(res.inequal.perSet)}`
            + ' (каждая точка чертежа хотя бы в одном);' : '')
        + ` конфигураций ${nice(res.inequal.configs)}`
        + (res.inequal.checked ? `; проверено ${nice(res.inequal.checked)}` : '')
        + (res.inequal.cramped
          ? '; случайных чертежей разыграно столько, сколько влезло в память —'
            + ' по ним меряются тождества, и просмотрены они не все' : '')
        + (res.inequal.refuted ? `; проверка отвергла ${nice(res.inequal.refuted)}` : '')
        + '</p>');
      const w = res.inequal.why ?? {};
      detail.push('<p class="gen-stat">отсеяно у неравенств: постоянная не узнаётся '
        + nice(w.unrecognized ?? 0)
        + ', это алгебра, а не геометрия ' + nice(w.algebra ?? 0)
        + ', очевидных ' + nice(w.obvious ?? 0)
        + ', часть содержится в целом ' + nice(w.trivial ?? 0)
        + ', вырожденных равенств ' + nice(w.identity ?? 0)
        + ', следует из других находок ' + nice((w.implied ?? 0) + (w.dependent ?? 0))
        + '</p>');
    }

    // ЧТО ЕЗДИТ И ЧТО СТОИТ — тоже сверху: вся выдача читается через это.
    if (res.locus)
      parts.push('<p class="gen-stat">задача на ГМТ: движется <b>'
        + escapeHtml(res.locus.along.map(a => a.on ? `${a.name} по ${a.on}` : `${a.name} по плоскости`)
          .join(', ')) + '</b>'
        + (res.locus.chosen ? ' (подвижную выбрал генератор)' : '')
        + `; в мире неподвижных ${nice(res.locus.fixed)}, подвижных ${nice(res.locus.movingObjs)}`
        + (res.locus.alwaysTrue
          ? `; верных и без движения отброшено ${nice(res.locus.alwaysTrue)}` : '')
        + (res.locus.unproven
          ? `; у ${nice(res.locus.unproven)} проверить без движения не вышло` : '')
        + '</p>');

    // ПОСЫЛКА НАЗЫВАЕТСЯ ВСЛУХ И СВЕРХУ. Всё, что ниже, верно только при ней, и
    // прочесть выдачу, не зная условия, значит прочесть её неверно.
    if (res.hypothesis)
      parts.push(`<p class="gen-stat">условная теорема${res.hypothesis.invented ? ' (посылку выбрал генератор)' : ''}`
        + ` при <b>${escapeHtml(res.hypothesis.conds.join(' и '))}</b>`
        + ` (условия добивались точкой ${escapeHtml(res.hypothesis.movable ?? '—')})`
        + (res.hypothesis.alwaysTrue
          ? `; верных и без условия отброшено ${nice(res.hypothesis.alwaysTrue)}` : '')
        + (res.hypothesis.unproven
          ? `; у ${nice(res.hypothesis.unproven)} проверить без условия не вышло — `
            + 'на свободном чертеже построение разваливается' : '')
        + '</p>');

    detail.push(`<p class="gen-stat">условие: ${res.scene.point} точек, ${res.scene.line} прямых,`
      + ` ${res.scene.circle} окружностей → мир из ${nice(res.closure.counts.point
        + res.closure.counts.line + res.closure.counts.circle)} объектов`
      + ` (${nice(res.closure.counts.point)} точек, ${nice(res.closure.counts.line)} прямых,`
      + ` ${nice(res.closure.counts.circle)} окружностей) за ${res.closure.ms} мс`
      + (res.closure.junctions ? `, из них ${nice(res.closure.junctions)} точек схождения` : '')
      + '</p>');

    // ЧТО ОБЕЩАЛИ И ЧТО ВЫШЛО — рядом. Прогноз за пределами разведанных слоёв
    // это оценка, и ошибаться она может в разы; молчать об этом хуже, чем
    // показать обе цифры и дать пользователю судить самому.
    if (res.forecast?.counts) {
      const f = res.forecast;
      const ftotal = f.counts.point + f.counts.line + f.counts.circle;
      const real = res.closure.counts.point + res.closure.counts.line + res.closure.counts.circle;
      const off = real ? Math.abs(ftotal - real) / real : 0;
      if (off > 0.25)
        detail.push(`<p class="gen-hint">прогноз обещал ${nice(Math.round(ftotal))} объектов`
          + ` (${nice(f.counts.point)} точек, ${nice(f.counts.line)} прямых) и замыкание`
          + ` около ${Math.round((f.closureMs ?? 0) / 1000)} с — разошлось с`
          + ' действительностью. За разведанными слоями прогноз считает по формулам,'
          + ' а склейку объектов формулой не предскажешь.</p>');
    }

    if (res.closure.full)
      parts.push('<p class="warn">мир упёрся в потолок: поднимите «потолок мира» или урежьте построения</p>');
    if (res.closure.capped.length)
      detail.push(`<p class="gen-hint">упёрлось в свой лимит: ${res.closure.capped.map(n =>
        escapeHtml(OPS[n]?.text ?? n)).join(', ')}</p>`);

    const found = res.timing.reduce((s, t) => s + t.found, 0);
    detail.push('<p class="gen-stat">найдено ' + nice(found) + ': '
      + res.timing.filter(t => t.found || t.failed).map(t =>
        `${escapeHtml(t.text)} — ${nice(t.found)}${t.failed ? ' (сбой)' : ''} за ${t.ms} мс`).join('; ')
      + '</p>');
    for (const t of res.timing) if (t.failed)
      parts.push(`<p class="warn">${escapeHtml(t.text)}: ${escapeHtml(t.failed)}</p>`);
    // «Просмотрено не всё» обязано быть сказано вслух: иначе короткая выдача
    // неотличима от «таких теорем нет», а это совсем разные вещи.
    for (const t of res.timing) if (t.truncated)
      parts.push(`<p class="warn">${escapeHtml(t.text)}: перебор оборван на `
        + `${nice(t.truncated.done)} ${escapeHtml(t.truncated.what)} из ${nice(t.truncated.total)}.`
        + ' Найденное на этом отрезке при вас, но просмотрено не всё — часть теорем'
        + ' не найдена. Уменьшите мир, а не ждите дольше.</p>');

    // Прогноз считал по ОБЪЯВЛЕННОЙ симметрии, а поиск идёт по подтверждённой.
    // Если построение её не подтвердило, обещанные минуты превращаются в часы —
    // и сказать об этом надо крупно, а не строкой отчёта.
    if (settings().symmetryGroups.length && (res.symmetryFound ?? 1) <= 1)
      parts.push('<p class="warn">симметрия не сработала: '
        + escapeHtml(res.symmetryWhy ?? 'причина не установлена')
        + '. Поиск шёл полным перебором, а не по орбитам, и потому занял'
        + ' больше обещанного прогнозом.</p>');

    const d = res.dropped ?? {};
    detail.push('<p class="gen-stat">отсеяно: следствий построения ' + nice(d.fromConstruction ?? 0)
      + (d.degenerate ? ', вырожденных ' + nice(d.degenerate) : '')
      + ', по счёту углов ' + nice(d.angleChase ?? 0)
      // Обрыв приведения называется вслух: ошибка в безопасную сторону,
      // но «сито местами не отработало» — это не то же, что «всё просеяно».
      + (d.angleGaveUp ? ` <span class="warn">(счёт углов сдался по пределам`
        + ` ${nice(d.angleGaveUp)} раз — столько фактов не просеяно)</span>` : '')
      + ', копий ' + nice(d.copies ?? 0)
      + ', по симметрии условия ' + nice(d.symmetric ?? 0)
      + (d.independent ? ', не зависят от ключевых ' + nice(d.independent) : '')
      + (res.refuted ? `; не подтвердилось на свежих конфигурациях ${nice(res.refuted)}` : '')
      + (res.symmetryOrder > 1 ? `. Симметрий у условия: ${res.symmetryOrder}` : '')
      + '</p>');

    if (res.stoppedStages?.length)
      parts.push(`<p class="gen-hint">оборвано по вашей просьбе: ${res.stoppedStages.map(escapeHtml).join(', ')}`
        + ' — показано то, что успелось</p>');
    if (res.screenFailed)
      parts.push(`<p class="warn">отсев не отработал: ${escapeHtml(res.screenFailed)}</p>`);

    // Вопросик — первым: он и открывается там, где на него смотрят.
    if (detail.length)
      parts.unshift('<details class="gen-diag"><summary title="как считали">?</summary><div>'
        + detail.join('') + '</div></details>');

    if (!res.kept.length) {
      parts.push('<p class="gen-hint">неочевидного не нашлось. Стоит добавить построений,'
        + ' поднять число слоёв или снять лимиты — либо отметить меньше ключевых объектов.</p>');
      say(parts.join(''));
      return;
    }

    parts.push(`<p class="gen-stat gen-left">осталось ${nice(res.kept.length)}: `
      + '<button type="button" class="chip gc">убрать мусор</button>'
      + ' <button type="button" class="chip dump">скопировать чертёж для разбора</button></p>'
      + '<ol class="gen-facts"></ol>');
    say(parts.join(''));
    fillFacts(res, report.querySelector('ol.gen-facts'));
    fitDrawing(res);
  }

  // ЧЕРТЁЖ ДОВОДИТСЯ ДО УСЛОВИЯ СРАЗУ ПОСЛЕ ПРОГОНА.
  //
  // Вся выдача верна на поверхности условия, а нарисованное на ней не лежит: на
  // экране эти факты ЛОЖНЫ, и первое, что делает человек, — проверяет мышью и
  // видит неправду. Поэтому точки, которыми условия и добивались, переставляются
  // в решённые места; остальные остаются ровно там, где нарисованы, так что
  // чертёж узнаваем и правится дальше как обычно.
  //
  // Двигать чужой чертёж молча нельзя: сказано, что сдвинулось, и рядом стоит
  // «вернуть как было».
  let fitUndo = null;
  function fitDrawing(res) {
    const moved = res.hypothesis?.fit;
    const applet = window.ggbApplet;
    if (!res.hypothesis) return;
    if (!moved?.length || !applet) {
      report.insertAdjacentHTML('beforeend', '<p class="warn">подогнать чертёж под условие'
        + ' не удалось: на экране эти факты будут ложны, потому что нарисованное условию'
        + ' не удовлетворяет</p>');
      return;
    }
    fitUndo = moved.map(m => ({ name: m.name, xy: m.from }));
    for (const m of moved) {
      // Точка могла оказаться несвободной — такую GeoGebra не подвинет, и это
      // законный исход: значит условия добивались не ею.
      try { applet.evalCommand(`SetCoords(${m.name},${m.to[0]},${m.to[1]})`); }
      catch { /* не подвинулась — и не надо */ }
    }
    report.insertAdjacentHTML('beforeend',
      '<p class="gen-stat gen-left">чертёж подогнан под условие: переставлены '
      + moved.map(m => escapeHtml(m.name)).join(', ')
      + ', остальное на своих местах '
      + '<button type="button" class="chip fit-undo">вернуть как было</button></p>');
  }

  // УБРАТЬ МУСОР — тот же отбор, что и у «случайной задачи».
  //
  // Сито оставляет неочевидное, но не смотрит, НУЖНО ли теореме условие: факт,
  // который верен и без половины данных, сито проходит честно, а задачей не
  // является. «Случайная задача» отбраковывает такие обобщателем, и делает это
  // молча — по одному факту, пока не найдётся годный. Здесь тот же отбор, но по
  // всей выдаче и с показанным счётом.
  //
  // Стоит это дорого: одно ослабление — один пересчёт конуса на другой сцене,
  // и ослаблений у факта столько же, сколько данных в задаче. Поэтому считается
  // ТОЛЬКО ПО ПРОСЬБЕ, порциями и с уступкой кадра — иначе вкладка замирает.
  //
  // Обобщение до носителя («верно для любой точки BC») мусором НЕ СЧИТАЕТСЯ:
  // оно теорему усиливает, а не опустошает, — ровно как и в «случайной задаче».
  let gcRun = 0;
  // ЧЕРТЁЖ НАРУЖУ — ЧТОБЫ РАЗБИРАТЬ ПО ТОМУ ЖЕ, ЧТО ВИДЕЛ ГЕНЕРАТОР.
  //
  // «У меня не находится» и «у меня находится» — это про два разных чертежа,
  // пока чертёж не передан целиком. Пересказ словами теряет ровно то, что решает:
  // проведена окружность через три точки или через центр и точку, какие команды
  // отдала GeoGebra, где что нарисовано. Здесь берётся СЛЕД — то самое, из чего
  // генератор строит мир, — и настройки прогона к нему.
  function dumpDrawing(btn) {
    const trace = (engine.trace ?? []).map(t => ({
      name: t.name, type: t.type, cmd: t.cmd,
      parsed: t.parsed ? { name: t.parsed.name, args: (t.parsed.args ?? []).map(String) } : null,
    }));
    const xy = {};
    const app = window.ggbApplet ?? null;
    // СВОБОДНЫЕ ТОЧКИ В СЛЕД НЕ ПОПАДАЮТ — а без них чертёж не восстановить: это
    // ровно те точки, от которых всё и пляшет. Имена берём из словарей движка.
    const named = new Set(trace.map(t => t.name));
    for (const m of [engine.pointExpr, engine.lineDefs, engine.circleDefs])
      for (const [n] of m ?? []) named.add(n);
    for (const n of named) {
      if (!app) break;
      try {
        const x = app.getXcoord(n), y = app.getYcoord(n);
        if (Number.isFinite(x) && Number.isFinite(y)) xy[n] = [x, y];
      } catch { /* не точка — координат нет, и ладно */ }
    }
    const s = settings();
    const dump = {
      штамп: BUILD_STAMP,
      trace,
      aux: [...(engine.auxObjects ?? [])],
      xy,
      настройки: {
        // Бесконечный предел построения JSON записать не умеет и кладёт null;
        // пишем словом, чтобы «null» не читалось как «не строить вовсе».
        selection: Object.fromEntries(Object.entries(s.selection)
          .map(([k, v]) => [k, v === Infinity ? 'без предела' : v])), layers: s.layers, maxObjects: s.maxObjects,
        essential: s.essential, predicates: s.predicates, random: s.random,
        heavyOverGiven: s.heavyOverGiven, seed: s.seed,
        locus: s.locus, hypothesis: s.hypothesis, inequal: s.inequal,
      },
    };
    const text = JSON.stringify(dump, null, 1);
    const done = ok => { btn.textContent = ok ? `скопировано (${nice(text.length)} знаков)`
      : 'скопировать не вышло — откройте консоль, чертёж выведен туда'; };
    try {
      navigator.clipboard.writeText(text).then(() => done(true), () => { console.log(text); done(false); });
    } catch { console.log(text); done(false); }
  }

  async function collectGarbage(btn) {
    if (!last?.kept?.length) return;
    // ПОД ПОСЫЛКОЙ ЭТОТ ОТБОР НЕ РАБОТАЕТ, и врать об этом нельзя.
    //
    // Обобщатор ослабляет условие и перепроверяет факт на СВОБОДНОЙ сцене — а
    // под посылкой факт на свободной сцене неверен сам по себе. Ответ выйдет не
    // «условие лишнее», а «условие существенно» у всего подряд, то есть отбор
    // не отсеет ничего и создаст ложное впечатление, будто выдача просеяна.
    if (last.hypothesis) {
      const line = btn.closest('p');
      line.innerHTML = `осталось ${nice(last.kept.length)}: `
        + '<span class="gen-cost">под посылкой мусор не убрать — обобщатор ослабляет '
        + 'условие на свободном чертеже, где сама теорема неверна</span>';
      return;
    }
    // И В ЗАДАЧЕ О ГМТ — ПО ТОЙ ЖЕ ПРИЧИНЕ.
    //
    // Обобщатор проверяет ослабление на СВОБОДНОЙ сцене, где все точки
    // равноправны. А утверждение «GH касается неподвижной окружности» на такой
    // сцене не просто неверно — оно бессмысленно: неподвижного там нет вовсе,
    // потому что не движется ничто. Ответы выходили произвольные, и отбор,
    // вместо того чтобы просеять выдачу, создавал впечатление, будто просеял.
    //
    // Своя проверка у задачи о ГМТ уже есть и идёт сама: «верно и без движения»
    // отбрасывает то, что не держится за движение (см. locus.js).
    if (last.locus) {
      const line = btn.closest('p');
      line.innerHTML = `осталось ${nice(last.kept.length)}: `
        + '<span class="gen-cost">в задаче о ГМТ мусор этим не убрать — обобщатор '
        + 'судит по свободному чертежу, где ничто не движется и «неподвижного» нет. '
        + 'Отбор «верно и без движения» уже прошёл при генерации</span>';
      return;
    }
    const mine = ++gcRun;
    const line = btn.closest('p');
    btn.disabled = true;
    const total = last.kept.length;
    const good = [];
    for (let i = 0; i < total; i++) {
      if (mine !== gcRun) return;
      let g = null;
      try {
        const f = last.kept[i];
        g = f.type === 'inequality'
          ? generalizeMetric(f, { world: last.world, steps: last.steps, visible: last.visible })
          : generalizeFact(f, last.world, {
            steps: last.steps, visible: last.visible, K: 8, seed: 909090,
          });
      } catch { g = null; }
      if (!g || !g.wider.length) good.push(i);
      if (i % 5 === 4) {
        btn.textContent = `проверяю ${nice(i + 1)} из ${nice(total)}…`;
        await new Promise(r => setTimeout(r, 0));
      }
    }
    if (mine !== gcRun) return;
    line.innerHTML = `осталось ${nice(good.length)} из ${nice(total)}: мусор убран `
      + '<button type="button" class="chip gc-undo">вернуть всё</button>';
    const list = report.querySelector('ol.gen-facts');
    if (list) { list.innerHTML = ''; fillFacts(last, list, good); }
  }

  // ОДИН ПУНКТ ВЫДАЧИ.
  //
  // ОБОБЩЕНИЕ показывается рядом с фактом: без чего он верен и что в нём не
  // участвует. Это и про силу утверждения (условие оказалось лишним — значит
  // теорема шире), и про интересность (половина данных не при чём — значит
  // теорема была про меньшую фигуру).
  function factItem(f, i, res) {
    // У НЕРАВЕНСТВА СВОЯ СТРОКА.
    //
    // «Обобщить» ему не по адресу: обобщатель ослабляет условия равенства, а тут
    // утверждение не про совпадение объектов, а про границу. Зато есть что
    // сказать вместо этого — случай равенства: он половина ценности неравенства.
    if (f.type === 'inequality')
      return `<li data-fact="${i}"><span class="gen-weight">${(f.objs ?? []).length}</span> `
        + (f.kind === 'identity'
          ? `<span class="gen-cost">${f.value ? 'найдите' : 'тождество'}</span> ` : '')
        + withSubscripts(escapeHtml(f.text))
        + (f.equality
          ? ` <span class="gen-cost">${f.limit ? 'равенство в пределе' : 'равенство'}:`
            + ` ${escapeHtml(f.equality)}</span>` : '')
        + (f.family ? ' <span class="gen-wider">равенство на целом семействе фигур</span>' : '')
        + (f.when?.length ? ` <span class="gen-wider">при ${escapeHtml(f.when.join(' и '))}</span>` : '')
        // РЕЗКАЯ ЛИ ПОСТОЯННАЯ — ВИДНО СРАЗУ, И ЭТО ЧЕСТНЕЕ МОЛЧАНИЯ.
        //
        // При быстрой проверке спрашивали одно: не пробита ли граница. Значит
        // «≤ 1» может стоять там, где точная граница 0,99999975, — утверждение
        // верное, но оценка не наилучшая. Выдавать такое за резкое нельзя.
        + (f.dir !== 'eq' && f.sharp === false
          ? ` <span class="gen-cost">${f.unchecked ? 'не проверялось'
            : 'постоянная, возможно, не наилучшая'}</span>` : '')
        + ' <button type="button" class="chip draw" data-fact="' + i + '">нарисовать</button>'
        + ' <button type="button" class="chip statement" data-fact="' + i + '">условие</button>'
      + ' <button type="button" class="chip save" data-fact="' + i + '">скачать</button>'
        + ' <button type="button" class="chip save" data-fact="' + i + '">скачать</button>'
        // Полная проверка одного факта идёт полсекунды — задавать её всем сразу
        // дорого, а тому, что приглянулось, в самый раз.
        + (f.dir !== 'eq' && f.sharp === false
          ? ' <button type="button" class="chip recheck" data-fact="' + i + '">проверить</button>' : '')
        + ' <button type="button" class="chip wider" data-fact="' + i + '">обобщить</button></li>';
    // СКОЛЬКО ПОСТРОЕНИЙ ПРИДЁТСЯ ВВЕСТИ, ЧТОБЫ ЭТО ВЫГОВОРИТЬ.
    //
    // Главная мерка содержательности, и её надо видеть глазами. Замерено на
    // четырёхточечном чертеже: у верхних фактов два-пять построений, у нижних
    // доходит до ста пятнадцати — «докажите, что AR = AT = UV = BC = WX» после
    // двадцати шести вспомогательных строк. Утверждение верное, задача никакая.
    const cost = (f.aux ?? 0) > 4
      ? ` <span class="gen-cost">+${f.aux} построений</span>` : '';
    const idle = (f.idle ?? []).length
      ? `не участвует: ${f.idle.join(", ")}` : '';
    return `<li data-fact="${i}"><span class="gen-weight">${substance(f)}</span> `
      + withSubscripts(escapeHtml(statement(f, res.world)))
      + (f.symmetricCopies ? ` <span class="gen-cost">и ещё ${f.symmetricCopies} по симметрии</span>` : '')
      + cost
      + (idle ? ` <span class="gen-cost">${escapeHtml(idle)}</span>` : '')
      + (f.support && f.support.ok * 2 < f.support.of
        ? ` <span class="gen-wider">проверено лишь на ${f.support.ok} конфигурациях из ${f.support.of}:`
          + ' объект существует не во всех — доверия меньше</span>' : '')
      + ' <button type="button" class="chip draw" data-fact="' + i + '">нарисовать</button>'
      + ' <button type="button" class="chip statement" data-fact="' + i + '">условие</button>'
      + ' <button type="button" class="chip wider" data-fact="' + i + '">обобщить</button></li>';
  }

  // ВЫДАЁТСЯ ВСЁ НАЙДЕННОЕ, НО ПОРЦИЯМИ.
  //
  // «Показаны первые двести» прятали ровно то, ради чего прогон и затевался:
  // порядок в выдаче — по виду утверждения и по номерам объектов, а не по
  // интересности, так что за двухсотым пунктом лежит ничем не худшее.
  //
  // Но и одной строкой список не выложить: десятки тысяч пунктов в innerHTML
  // морозят вкладку на минуты, а замершая страница — тот же обман, что и
  // урезанная выдача. Поэтому список дописывается кусками, и между кусками
  // управление возвращается браузеру: первая сотня видна сразу, прокрутка
  // живая, остальное подтягивается само.
  const LIST_CHUNK = 200;
  let listRun = 0;
  // Показать можно не всю выдачу, а выбранные номера (см. «убрать мусор»).
  // Номера СКВОЗНЫЕ, из res.kept: на них ссылаются кнопки «нарисовать»,
  // «условие», «обобщить», и после уборки они обязаны указывать туда же.
  async function fillFacts(res, list, rows = null) {
    if (!list) return;
    // Выдачу могли сменить, пока мы дописывали (новый прогон, случайная
    // задача). Тогда дописывать некуда, и старая порция обязана уйти молча.
    const mine = ++listRun;
    const idx = rows ?? res.kept.map((_, i) => i);
    for (let from = 0; from < idx.length; from += LIST_CHUNK) {
      if (mine !== listRun || !list.isConnected) return;
      const html = [];
      const to = Math.min(from + LIST_CHUNK, idx.length);
      for (let j = from; j < to; j++) html.push(factItem(res.kept[idx[j]], idx[j], res));
      list.insertAdjacentHTML('beforeend', html.join(''));
      if (to < idx.length) await new Promise(r => setTimeout(r, 0));
    }
  }

  // ---- рисование ------------------------------------------------------------

  // ОБЪЕКТ ЧИСЛАМИ — на случай, когда построением не вышло.
  //
  // Точка задаётся парой, прямая — уравнением nx·x + ny·y = c, окружность —
  // центром и радиусом. Числа берутся из посчитанного значения (см. want), то
  // есть из проигрывания построения по координатам с экрана.
  function literalCommand(name, want) {
    const v = want?.v;
    if (!Array.isArray(v) || !v.every(x => Number.isFinite(x))) return null;
    const num = x => (Math.abs(x) < 1e-12 ? 0 : Number(x.toPrecision(12)));
    if (want.kind === KIND.point) return `${name}=(${num(v[0])},${num(v[1])})`;
    // Прямая — уравнением: у GeoGebra это законная запись объекта.
    if (want.kind === KIND.line) return `${name}: ${num(v[0])}x + ${num(v[1])}y = ${num(v[2])}`;
    if (want.kind === KIND.circle && v[2] > 0)
      return `${name}=Circle((${num(v[0])},${num(v[1])}),${num(v[2])})`;
    return null;
  }

  // НАСКОЛЬКО ПОСТРОЕННОЕ РАЗОШЛОСЬ С ПОСЧИТАННЫМ.
  //
  // Точку GeoGebra отдаёт координатами, а прямую и окружность — нет. Зато
  // отдаёт РАССТОЯНИЕ: заводим временное число, спрашиваем его и убираем. Это
  // и есть общая мера, годная для всех видов сразу.
  //
  // Без неё у касательной из точки — а их две — рисовалась та, что первой
  // пришла GeoGebra в голову, дальше по ней строились точки, и расходилось всё.
  function missBy(applet, step) {
    const want = step.want;
    if (!want) return null;
    try {
      if (want.kind === 0) {
        const dx = applet.getXcoord(step.name) - want.v[0];
        const dy = applet.getYcoord(step.name) - want.v[1];
        return Math.hypot(dx, dy) / (1 + Math.hypot(want.v[0], want.v[1]));
      }
      // Прямая и окружность: сравниваем расстояния до трёх опорных точек.
      const probes = (window.__genProbes ?? []).slice(0, 3);
      if (!probes.length) return null;
      let worst = 0;
      for (const q of probes) {
        const tmp = `gProbe${Math.floor(Math.random() * 1e6)}`;
        applet.evalCommand(`${tmp}=Distance(${q.name},${step.name})`);
        const got = applet.exists(tmp) ? applet.getValue(tmp) : null;
        if (applet.exists(tmp)) applet.deleteObject(tmp);
        if (got === null || !Number.isFinite(got)) return null;
        const need = want.kind === 1
          ? Math.abs(want.v[0] * q.x + want.v[1] * q.y - want.v[2])
          : Math.abs(Math.hypot(q.x - want.v[0], q.y - want.v[1]) - want.v[2]);
        worst = Math.max(worst, Math.abs(got - need) / (1 + need));
      }
      return worst;
    } catch { return null; }
  }

  report.addEventListener('click', async event => {
    // Условие задачи. Запись факта точна, но нечитаема: она показывает, ЧЕМ
    // объект построен, а не как его назвать. Здесь то же самое разворачивается
    // в «дано» по шагам и «докажите» — текст, который можно дать человеку.
    const ask = event.target.closest('button.statement');
    if (ask && last) {
      const li = ask.closest('li');
      const already = li.querySelector('.gen-statement');
      if (already) { already.remove(); ask.textContent = 'условие'; return; }
      // ЗАПИСЬ ПОКОРОЧЕ — сразу, а не по отдельной кнопке.
      //
      // Биссектриса угла DAE и биссектриса угла BAC — один и тот же объект,
      // если B на луче AD, а C на луче AE; какая из записей попала в мир, решил
      // порядок перебора. В условие надо ту, где точек меньше: она короче и
      // честнее показывает, о чём теорема. Подстановки уже посчитаны при
      // разметке и помнятся при мире, так что это ничего не стоит.
      const chosen = last.kept[Number(ask.dataset.fact)];
      let swap = null;
      try {
        swap = new Map(redundantGivens(chosen, last.world).map(r => [r.obj, r.byObj]));
      } catch { swap = null; }
      const text = inUiLanguage(() => problemText(chosen, last.world,
        { conditions: conditionsOf(last.steps, last.kindOf), swap, redef: chosen.redef,
          hypothesis: last.hypothesis?.conds,
          locus: last.locus ? { moving: last.locus.moving, along: last.locus.along, fixed: chosen?.locus?.fixed } : null }));
      const box = document.createElement('div');
      box.className = 'gen-statement';
      const pre = document.createElement('pre');
      pre.innerHTML = withSubscripts(escapeHtml(text));
      const copy = document.createElement('button');
      copy.type = 'button';
      copy.className = 'canon';
      copy.textContent = 'скопировать';
      copy.addEventListener('click', () => {
        navigator.clipboard?.writeText(text).then(
          () => { copy.textContent = 'скопировано'; },
          () => { copy.textContent = 'буфер недоступен'; });
      });
      box.append(pre, copy);
      li.append(box);
      ask.textContent = 'скрыть условие';
      return;
    }

    // ОБОБЩЕНИЕ ПО ПРОСЬБЕ. Считается не для всей выдачи, а для одного факта:
    // каждое ослабление условия — это отдельный пересчёт на другой сцене, и
    // делать их тысячами незачем. Спрашивают обычно про одну теорему.
    const undoFit = event.target.closest('button.fit-undo');
    if (undoFit && fitUndo) {
      const applet = window.ggbApplet;
      for (const p of fitUndo) {
        try { applet?.evalCommand(`SetCoords(${p.name},${p.xy[0]},${p.xy[1]})`); }
        catch { /* ничего не поделать */ }
      }
      undoFit.closest('p').textContent = 'чертёж возвращён как был — но выдача верна'
        + ' только под условием, и на этом чертеже она ложна';
      fitUndo = null;
      return;
    }
    const gc = event.target.closest('button.gc');
    if (gc && last) { collectGarbage(gc); return; }
    const dump = event.target.closest('button.dump');
    if (dump && last) { dumpDrawing(dump); return; }
    const undo = event.target.closest('button.gc-undo');
    if (undo && last) {
      const line = undo.closest('p');
      line.innerHTML = `осталось ${nice(last.kept.length)}: `
        + '<button type="button" class="chip gc">убрать мусор</button>';
      const list = report.querySelector('ol.gen-facts');
      if (list) { list.innerHTML = ''; fillFacts(last, list); }
      return;
    }
    // ПРОВЕРИТЬ ОДНО НЕРАВЕНСТВО ПО ТРЕБОВАНИЮ.
    //
    // Быстрая проверка отвечает только на «не пробита ли граница», без проверки —
    // и на это не отвечает. Вопрос «наилучшая ли постоянная» стоит полсекунды на
    // факт: всем двадцати тысячам его не задать, а выбранному — запросто.
    const rech = event.target.closest('button.recheck');
    if (rech && last) {
      const fact = last.kept[Number(rech.dataset.fact)];
      if (!fact) return;
      rech.disabled = true;
      rech.textContent = 'проверяю…';
      (async () => {
        let res = null, failed = null;
        try {
          res = await recheckFact(fact, { world: last.world, steps: last.steps,
                                          visible: last.visible });
        } catch (e) { failed = e.message; }
        const note = document.createElement('span');
        if (failed) {
          note.className = 'warn';
          note.textContent = ` проверка не вышла: ${failed}`;
        } else if (res.ok) {
          // Постоянная могла уточниться: быстрая берёт ту, что узналась по
          // одному заходу, полная — по трём. Тогда и запись факта другая.
          note.className = 'gen-wider';
          note.textContent = res.changed
            ? ` проверено: постоянная на деле ${res.lam}`
            : ' проверено: постоянная наилучшая'
              + (res.limit ? ' (равенство достигается в пределе)' : '');
          fact.sharp = true;
          fact.unchecked = false;
          if (res.changed) { fact.lam = res.lam; fact.lamValue = res.lamValue; }
          fact.limit = res.limit;
        } else {
          note.className = 'warn';
          note.textContent = ` проверка ОТВЕРГЛА: ${res.why}`;
          fact.refutedBy = res.why;
        }
        rech.replaceWith(note);
      })();
      return;
    }
    const wide = event.target.closest('button.wider');
    if (wide && last) {
      const li = wide.closest('li');
      const shown = li.querySelector('.gen-general');
      if (shown) { shown.remove(); wide.textContent = 'обобщить'; return; }
      const fact = last.kept[Number(wide.dataset.fact)];
      if (!fact) return;
      wide.disabled = true; wide.textContent = 'считаю…';
      // Пересчёт синхронный и недолгий, но уступить кадр надо: иначе кнопка
      // так и не успеет показать, что она нажата.
      setTimeout(() => {
        let res = null, failed = null, extra = [];
        try {
          // У НЕРАВЕНСТВ И ТОЖДЕСТВ ОБОБЩЕНИЕ СВОЁ.
          //
          // Вопрос тот же — можно ли брать точку где угодно, — а проверка другая:
          // у равенства спрашивают, совпали ли объекты, а тут держится ли ГРАНИЦА
          // (или постоянство отношения) на ослабленном чертеже.
          res = fact.type === 'inequality'
            ? generalizeMetric(fact, { world: last.world, steps: last.steps,
                                       visible: last.visible })
            : generalizeFact(fact, last.world, {
              steps: last.steps, visible: last.visible, K: 8, seed: 909090,
            });
          // Данная точка, чью роль играет другая: формально участвует, а по
          // существу лишняя (см. general.js).
          extra = fact.type === 'inequality' ? [] : redundantGivens(fact, last.world);
        } catch (e) { failed = e.message; }
        const box = document.createElement('div');
        box.className = 'gen-general';
        const parts = [];
        if (failed) parts.push(`<p class="warn">не вышло: ${escapeHtml(failed)}</p>`);
        else {
          const used = (fact.used ?? []).join(', ') || '—';
          parts.push(`<p>участвует: <b>${escapeHtml(used)}</b>`
            + ((fact.idle ?? []).length ? `; не участвует: ${escapeHtml(fact.idle.join(', '))}` : '')
            + '</p>');
          if (res.wider.length)
            parts.push('<p>теорема ШИРЕ условия — она верна и без этого:</p><ul>'
              + res.wider.map(r => `<li>${escapeHtml(r.text)}</li>`).join('') + '</ul>');
          if (res.needed.length)
            // Это про УСЛОВИЕ на точку, а не про саму точку: «D — точка на
            // окружности» снять нельзя, иначе теорема ложна. Одного имени мало —
            // непонятно, что именно нельзя снять.
            parts.push('<p>условие снять НЕЛЬЗЯ — без него теорема неверна:</p><ul>'
              + res.needed.map(r => `<li>${escapeHtml(r.text)}</li>`).join('') + '</ul>');
          // ОБОБЩЕНИЕ ДО НОСИТЕЛЯ. Условие снять нельзя, но держится оно не на
          // самом построении, а лишь на том, что точка лежит на такой-то прямой
          // (окружности). Это про СИЛУ формулировки: теорема не про середину
          // стороны, а про любую точку BC, — и сказать об этом стоит, даже когда
          // условие остаётся.
          //
          // Задачу это не портит и из «случайной задачи» её не выбрасывает: там
          // отсеивается только обобщение до всей плоскости (см. g.wider).
          if (res.onto?.length)
            parts.push('<p>условие остаётся, но теорема ШИРЕ, чем записана —'
              + ' она верна для любой точки носителя:</p><ul>'
              + res.onto.map(r => `<li>${escapeHtml(r.text)}</li>`).join('') + '</ul>');
          if (res.unknown.length)
            parts.push('<p class="gen-hint">проверить не удалось: '
              + res.unknown.map(r => escapeHtml(r.name)).join(', ')
              + ' — при ослаблении построение разваливается</p>');
          if (extra.length) {
            const row = r => `<li>${escapeHtml(r.name)} — её роль играет `
              + `${escapeHtml(r.by ?? 'другая точка')}`
              + (r.where.length ? ` (${escapeHtml(r.where.join(', '))})` : '')
              + '</li>';
            parts.push('<p>лишнее в условии — эти точки только строят другое, и то же самое'
              + ' строится без них:</p><ul>' + extra.map(row).join('') + '</ul>');
          }
          // ЧТО ИМЕННО ИСЧЕЗНЕТ — списком, а не по намёкам.
          //
          // Выбрасывается двоякое: то, чего в факте нет вовсе (не участвует), и
          // то, чью роль играет другая точка. Обе кнопки ниже убирают ровно это,
          // и знать заранее, что пропадёт с чертежа, спокойнее, чем обнаруживать
          // это post factum.
          const goes = [...new Set([...(fact.idle ?? []), ...extra.map(r => r.name)])];
          if (goes.length)
            parts.push('<p>из условия и с рисунка уйдут: <b>'
              + escapeHtml(goes.join(', ')) + '</b></p>');
          if (!res.checked)
            parts.push('<p class="gen-hint">ослаблять нечего: все участники — свободные точки чертежа</p>');
        }
        // Условие и рисунок БЕЗ ЛИШНЕГО. Лишнее — это данные, которых в факте
        // нет вовсе, и условия, без которых он всё равно верен: и то и другое
        // обобщатор только что посчитал.
        if (!failed) {
          parts.push('<p><button type="button" class="chip lean-text">условие без лишнего</button>'
            + ' <button type="button" class="chip lean-draw">рисунок без лишнего</button></p>');
        }
        box.innerHTML = parts.join('');
        li.append(box);
        if (!failed) {
          const relaxed = new Set(res.wider.map(r => r.name));
          const swap = new Map(extra.map(r => [r.obj, r.byObj]));
          const spare = new Set(extra.map(r => r.name));
          box.querySelector('.lean-text')?.addEventListener('click', ev => {
            const shownText = box.querySelector('.gen-statement');
            if (shownText) { shownText.remove(); ev.target.textContent = 'условие без лишнего'; return; }
            const text = inUiLanguage(() => problemText(fact, last.world,
              { conditions: conditionsOf(last.steps, last.kindOf), relaxed, swap,
                redef: fact.redef, hypothesis: last.hypothesis?.conds,
          locus: last.locus ? { moving: last.locus.moving, along: last.locus.along, fixed: fact?.locus?.fixed } : null }));
            const wrap = document.createElement('div');
            wrap.className = 'gen-statement';
            const pre = document.createElement('pre');
            pre.innerHTML = withSubscripts(escapeHtml(text));
            wrap.append(pre);
            box.append(wrap);
            ev.target.textContent = 'скрыть условие';
          });
          box.querySelector('.lean-draw')?.addEventListener('click', ev => {
            const applet = window.ggbApplet;
            if (!applet) return;
            // Прячем данные объекты, которых в факте нет: чертёж должен
            // показывать теорему, а не всё, что было нарисовано.
            // Лишнее — это и то, чего в факте нет вовсе, и то, чью роль играет
            // другая точка: второе формально участвует, а показывать его незачем.
            const used = new Set(fact.used ?? []);
            for (const n of spare) used.delete(n);
            for (const n of last.visible ?? [])
              if (!used.has(n) && applet.exists(n)) {
                hidden.add(n);
                applet.setVisible(n, false);
              }
            li.querySelector('button.draw')?.click();
            ev.target.textContent = 'лишнее спрятано';
            ev.target.disabled = true;
          });
        }
        wide.disabled = false;
        wide.textContent = 'скрыть обобщение';
      }, 0);
      return;
    }

    // СКАЧАТЬ НАХОДКУ.
    //
    // Файл должен показывать именно эту теорему, поэтому сперва она рисуется
    // (если ещё не нарисована), и только потом снимается полотно. Рисование
    // идёт своим чередом и кончается тем, что кнопка «нарисовать» гаснет, —
    // по ней и ждём, не дольше шести секунд: чертёж без части построений
    // лучше, чем зависшая кнопка.
    const saveButton = event.target.closest('button.save');
    if (saveButton && last) {
      const fact = last.kept[Number(saveButton.dataset.fact)];
      if (!fact) return;
      const li = saveButton.closest('li');
      const drawButton = li?.querySelector('button.draw');
      const was = saveButton.textContent;
      saveButton.disabled = true;
      try {
        if (drawButton && !drawButton.disabled) {
          saveButton.textContent = 'рисую…';
          drawButton.click();
          for (let i = 0; i < 60 && !drawButton.disabled; i++) {
            await new Promise(resolve => setTimeout(resolve, 100));
          }
        }
        saveButton.textContent = 'собираю…';
        const text = inUiLanguage(() => problemText(fact, last.world, {
          conditions: conditionsOf(last.steps, last.kindOf),
          redef: fact.redef,
          hypothesis: last.hypothesis?.conds,
          locus: last.locus
            ? { moving: last.locus.moving, along: last.locus.along, fixed: fact?.locus?.fixed }
            : null,
        }));
        const mod = await loadExport();
        mod.saveFound({
          text,
          applet: window.ggbApplet,
          configs: last.world?.K ?? null,
          confirmed: fact.confirmed ?? null,
          // Для рецензии: из чего считать обобщение. Сам разбор — в export.js,
          // панели незачем знать, из чего он складывается.
          fact,
          world: last.world,
          steps: last.steps,
          visible: last.visible,
        });
        saveButton.textContent = 'скачано';
      } catch (e) {
        saveButton.textContent = 'не вышло';
        saveButton.title = e.message;
        setTimeout(() => { saveButton.textContent = was; saveButton.disabled = false; }, 2000);
      }
      return;
    }

    const button = event.target.closest('button.draw');
    if (!button || !last) return;
    const fact = last.kept[Number(button.dataset.fact)];
    const applet = window.ggbApplet;
    if (!fact || !applet) return;

    // Ленивый модуль GeoGebra — до первой команды, а не после неудачи: иначе
    // первый же шаг с TriangleCenter отваливается, а с ним и всё, что на нём
    // стоит. Ждём не больше трёх секунд и в любом случае идём дальше.
    await ensureDiscrete(applet);

    const known = new Set();
    for (const map of [engine.pointExpr, engine.lineDefs, engine.circleDefs])
      for (const name of map?.keys() ?? []) known.add(name);

    // ЧЕГО ЖДАТЬ ОТ КАЖДОГО ШАГА.
    //
    // Построение проигрывается ещё раз по координатам с экрана. Нужно это для
    // построений с двумя ветвями: генератор и GeoGebra нумеруют точки
    // пересечения по-разному, и без сличения на чертёж попадала не та из двух —
    // молча, отчего равные отрезки выходили разной длины.
    // Имена берутся у САМОГО АППЛЕТА, а не из чертежа генератора: свободные
    // точки в чертёж не попадают (там только объекты, созданные командами), а
    // проигрывать построение надо именно от них. Без A, B, C проигрыш
    // разваливался на первом же шаге, и сличать точки было не с чем.
    const positions = [];
    for (const name of applet.getAllObjectNames() ?? []) {
      try {
        if (applet.exists(name) && applet.getObjectType(name) === 'point')
          positions.push({ kind: 'point', name, x: applet.getXcoord(name), y: applet.getYcoord(name) });
      } catch { /* объекта уже нет — не беда */ }
    }
    // Опорные точки для сличения прямых и окружностей — те же, по которым
    // проигрывалось построение.
    window.__genProbes = positions;
    let want = null;
    try { want = drawingValues(last.world, last.sceneFn, positions); } catch { want = null; }
    const plan = planFact(fact, last.world, { known, want });
    const made = [];
    const troubles = [];
    // ЗАПАСНЫЕ ЗАПИСИ И НЕПОЛНЫЙ ЧЕРТЁЖ.
    //
    // GeoGebra на одну и ту же геометрию отвечает по-разному: у точки вне
    // окружности Tangent даёт список из двух прямых, у точки на окружности —
    // одну прямую, и Element на ней падает. Угадать заранее нельзя, поэтому у
    // построения бывает несколько записей, и они пробуются по очереди.
    //
    // Сорвавшийся шаг больше НЕ обрывает построение целиком: раньше одна
    // неудачная команда оставляла чертёж наполовину пустым и без объяснения.
    // Теперь строится всё, что строится, а о несделанном говорится поимённо.
    for (const step of plan.steps) {
      if (applet.exists(step.name)) continue;
      const variants = step.cmds ?? [step.cmd];
      let done = false, lastErr = null, best = null;
      // Повтор нужен ПОСЛЕ ИСКЛЮЧЕНИЯ, а не только после тихой неудачи.
      //
      // Раньше повторный вызов стоял внутри try, сразу за первым, — и при
      // исключении (а ленивый модуль бросает именно его) до него не доходило
      // вовсе. Теперь каждая попытка со своим try.
      const fire = cmd => {
        try { applet.evalCommand(cmd); } catch (e) { lastErr = e.message; }
      };
      for (const cmd of variants) {
        fire(cmd);
        if (!applet.exists(step.name)) fire(cmd);
        if (!applet.exists(step.name)) continue;
        // Построилось — но ТО ЛИ. Если известно, чего ждать, сличаем; не сошлось
        // — пробуем следующий вариант, а лучший из отвергнутых держим про запас.
        const off = missBy(applet, step);
        if (off === null || off <= 1e-6) {
          drawn.push(step.name);
          made.push({ ...step, cmd });
          done = true;
          break;
        }
        if (!best || off < best.off) best = { cmd, off };
        applet.deleteObject(step.name);
      }
      // Ни один вариант не сошёлся точно — берём ближайший и говорим об этом.
      if (!done && best) {
        try { applet.evalCommand(best.cmd); } catch { /* уже пробовали */ }
        if (applet.exists(step.name)) {
          drawn.push(step.name);
          made.push({ ...step, cmd: best.cmd });
          done = true;
          troubles.push(`${step.label}: ни одна запись не дала посчитанную точку`
            + ` (разошлось на ${best.off.toPrecision(2)}) — нарисована ближайшая`);
        }
      }
      // ПОСЛЕДНИЙ ХОД: ПОСТРОИТЬ ПО КООРДИНАТАМ.
      //
      // Ни одна запись не прошла — а объект посчитан, и место его известно
      // точно: генератор проиграл построение по координатам с экрана. Значит
      // рисовать есть что, и оставлять чертёж дырявым незачем: ставим объект
      // числами и говорим об этом прямо.
      //
      // Такой объект не связан с чертежом: потянешь вершину — он останется на
      // месте. Поэтому он именно последний ход, а не первый.
      if (!done && step.want) {
        const cmd = literalCommand(step.name, step.want);
        if (cmd) {
          try { applet.evalCommand(cmd); } catch { /* и это не вышло */ }
          if (applet.exists(step.name)) {
            drawn.push(step.name);
            made.push({ ...step, cmd });
            done = true;
            troubles.push(`${step.label}: построением не вышло`
              + (lastErr ? ` (${lastErr})` : '')
              + ' — поставлено по координатам, за чертежом не следует');
          }
        }
      }
      if (!done) troubles.push(`${step.label}: ${variants[0]}${lastErr ? ` (${lastErr})` : ''}`);
    }
    const failed = troubles.length ? troubles[0] : null;

    // Построенное подкрашиваем: на плотном чертеже иначе не найти, что именно
    // добавилось. Доли, а НЕ 0..255 — SetColor принимает числа от нуля до
    // единицы, и «255,0,0» становится белым, то есть невидимым. Размеры как у
    // самого чертежа: у GeoGebra точка по умолчанию 3 и линия 3.
    for (const step of made) {
      try {
        // Оформление — у оформителя, а не здесь: тогда его можно менять из
        // настроек, и дорисованное перекрашивается вместе со всем остальным.
        // «prove» — то, что надо доказать: оно не дано, а утверждается.
        styler?.mark(step.name, step.dashed ? 'prove' : 'draw');
        // Подпись обязательна: без неё построенный объект на чертеже есть, а
        // сказать, который из них какой, нечем. Через API, а не командой:
        // имена вроде «H_{ABC}» в тексте команды разбираются не всегда.
        applet.setLabelVisible?.(step.name, true);
      } catch { /* стиль — украшение, из-за него терять построенное незачем */ }
    }

    button.disabled = true;
    // «Не вышло» — неправда, когда построилась половина. Говорим числом.
    button.textContent = troubles.length
      ? `построено ${made.length} из ${made.length + troubles.length}`
      : made.length ? `построено: ${made.length}` : 'уже на чертеже';
    const trouble = [...plan.problems, ...troubles].filter(Boolean);
    if (trouble.length) button.title = trouble.join('; ');

    // Расшифровка: чем каждый объект факта стал на чертеже. Предки строились и
    // раньше, но в отчёте они зовутся по построению, а на чертеже «g7», и
    // связать одно с другим было нечем.
    if (made.length || trouble.length) {
      const box = document.createElement('div');
      box.className = 'gen-plan';
      box.innerHTML = (made.length
        ? '<p>как построено:</p><ol>' + made.map(s =>
            `<li><code>${escapeHtml(s.name)}</code> = ${escapeHtml(s.cmd.slice(s.name.length + 1))}`
            + ` <span class="gen-cost">${escapeHtml(s.label)}</span></li>`).join('') + '</ol>'
        : '')
        + (trouble.length ? `<p class="warn">${escapeHtml(trouble.join('; '))}</p>` : '');
      button.closest('li')?.append(box);
    }
  });

  document.getElementById('clear-drawn').addEventListener('click', () => {
    const applet = window.ggbApplet;
    if (!applet || !drawn.length) return;
    // В обратном порядке: у поздних объектов ранние стоят в аргументах, и
    // удаление предка утащило бы потомка вместе с собой.
    for (const name of [...drawn].reverse()) if (applet.exists(name)) applet.deleteObject(name);
    drawn.length = 0;
    // Спрятанное возвращаем: чертёж пользователя должен вернуться целым.
    for (const name of hidden) if (applet.exists(name)) applet.setVisible(name, true);
    hidden.clear();
    for (const button of report.querySelectorAll('button.draw')) {
      button.disabled = false;
      button.textContent = 'нарисовать';
      button.removeAttribute('title');
    }
  });

  // ---- прогон ---------------------------------------------------------------

  const button = document.getElementById('run-gen');
  // Жетон идущего прогона: нужен, чтобы оборвать его снаружи.
  let running = null;

  async function run(extra = {}) {
    if (engine !== ENGINES.complex.bridge) {
      say('<p class="warn">генератор считает в обычных числах по вашему построению,'
        + ' а построение читается из Компланатора: переключите движок.</p>');
      return;
    }
    const s = settings();
    if (!Object.keys(s.selection).length) {
      say('<p class="warn">не выбрано ни одного построения: достраивать нечем</p>');
      return;
    }
    if (!s.predicates.length) {
      say('<p class="warn">не выбрано ни одного условия: искать нечего</p>');
      return;
    }

    button.disabled = true;
    const stop = new StopToken();
    // Наружу — чтобы поиск случайной задачи мог оборвать прогон целиком, а не
    // этап за нажатие.
    running = stop;
    stopper.hidden = false;
    stopper.disabled = false;
    const onStop = () => { stop.request(); stopper.textContent = 'обрываю этап…'; };
    stopper.textContent = 'хватит';
    stopper.addEventListener('click', onStop);

    const started = Date.now();
    try {
      const res = await generate(engine, {
        ...s,
        ...extra,
        applet: window.ggbApplet ?? null,
        stop,
        onProgress: text => say(`<p class="working">${escapeHtml(text)}</p>`),
      });
      renderResult(res, Date.now() - started);
    } catch (e) {
      say(`<p class="warn">не получилось: ${escapeHtml(e.message)}</p>`);
    } finally {
      running = null;
      button.disabled = false;
      stopper.hidden = true;
      stopper.removeEventListener('click', onStop);
    }
  }

  button.addEventListener('click', run);

  // СЛУЧАЙНАЯ ЗАДАЧА.
  //
  // Выдача генератора — это сотни фактов, и выбирать из них руками утомительно.
  // Кнопка делает выбор сама: прогоняет поиск с теми же настройками и берёт
  // ПЕРВУЮ теорему, которая
  //   * пережила отсев (значит не следует из построения и не берётся счётом
  //     углов — это уже проверено),
  //   * содержательна (объектов в ней больше необходимого),
  //   * пользуется всеми данными задачи (ничего лишнего в условии),
  //   * и НЕ ОБОБЩАЕТСЯ — ни одно условие снять нельзя.
  //
  // Последнее и есть главный признак: если условие можно ослабить, значит
  // задача была сформулирована уже, чем следует, и настоящая теорема — другая.
  //
  // Порядок перебора случайный, с зерном от часов: две подряд нажатые кнопки
  // дают разные задачи.
  const lucky = document.getElementById('lucky-gen');
  let luckyStop = false;

  // Ищет, ПОКА НЕ НАЙДЁТ.
  //
  // Одного прогона мало: на маленьком мире годной задачи может не оказаться
  // вовсе — все факты либо тривиальны, либо обобщаются. Поэтому кнопка ищет
  // ПОКА НЕ НАЙДЁТ, без счётчика попыток: своей границы у поиска нет, границу
  // ставит пользователь. Останавливает она же — на время поиска она становится
  // «прекратить».
  //
  // ЧТО МЕНЯЕТСЯ МЕЖДУ ПОПЫТКАМИ — вопрос не праздный. Одного зерна мало:
  // замыкание от него не зависит вовсе. Без случайного отбора наборов оно
  // строится ОДНО И ТО ЖЕ при любом зерне — меняются только числа, а значит и
  // факты выходят те же. Перебирать так можно вечно без толку.
  //
  // Поэтому со второй попытки включается случайный отбор наборов со своим
  // зерном: каждая попытка строит ДРУГУЮ часть замыкания. Потолок при этом
  // растёт, но не больше чем втрое, а число слоёв не трогается вовсе — слой
  // меняет мир на порядок, и подставлять его молча нельзя: это верный способ
  // подвесить вкладку.
  //
  // Ничего на странице при этом не перезагружается: меняется только отчёт.
  lucky?.addEventListener('click', async () => {
    if (lucky.dataset.busy) {
      // Просто поднять флаг мало: он проверяется МЕЖДУ попытками, а идущий
      // прогон может считать ещё минуту. Поэтому идущему прогону даётся
      // ЖЁСТКИЙ обрыв: «хватит» снимает один этап за нажатие, а здесь надо
      // снять все сразу.
      luckyStop = true;
      lucky.textContent = 'останавливаюсь…';
      running?.abort();
      return;
    }
    lucky.dataset.busy = '1';
    luckyStop = false;
    const was = 'случайная задача';
    lucky.textContent = 'прекратить';
    const base = Number(document.getElementById('gen-budget')?.value) || 1500;
    let attempt = 0, looked = 0, pool = 0;
    try {
      while (!luckyStop) {
        attempt++;
        const cap = Math.round(base * Math.min(3, 1 + 0.25 * (attempt - 1)));
        // Первая попытка — ровно то, что настроил пользователь. Дальше —
        // случайный отбор наборов, иначе замыкание каждый раз одно и то же.
        //
        // Оговорка про классические построения: они живут ТОЛЬКО в случайном
        // отборе, и если пользователь заказал им долю жребиев, то отбор нужен
        // уже на первой попытке — иначе заказ молча пропадает, а задача выходит
        // ровно такой пустой, из-за какой классику и заводили.
        const wantsClassic = Object.keys(settings().classic ?? {}).length > 0;
        const extra = attempt === 1
          ? { seed: 20260901, maxObjects: cap,
              ...(wantsClassic ? { random: true } : {}) }
          : { seed: 20260901 + attempt * 7919, maxObjects: cap,
              random: true, perLayer: null };
        try {
          await run(extra);
        } catch (e) {
          // Сорвавшаяся попытка не повод бросать поиск: берём следующую.
          say(`<p class="working">попытка ${attempt} сорвалась (${escapeHtml(e.message)})`
            + ' — пробую дальше…</p>');
          await new Promise(r => setTimeout(r, 30));
          continue;
        }
        if (luckyStop) break;
        const cand = (last?.kept ?? []).map((f, i) => ({ f, i }))
          .filter(({ f }) => substance(f) >= 1 && !(f.idle ?? []).length);
        pool = cand.length;
        // Перемешиваем: подряд нажатые кнопки должны давать разные задачи.
        let seed = (Date.now() ^ (Math.random() * 1e9)) >>> 0;
        const rnd = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 4294967296; };
        for (let i = cand.length - 1; i > 0; i--) {
          const j = Math.floor(rnd() * (i + 1));
          [cand[i], cand[j]] = [cand[j], cand[i]];
        }
        let picked = null;
        looked = 0;
        // ПОД ПОСЫЛКОЙ ОТБИРАЕТ УЖЕ САМ ПРОГОН.
        //
        // Обычно годность задачи решает обобщатель: факт, верный и без части
        // условия, задачей не считается. Под посылкой он не работает — ослабляет
        // на свободном чертеже, где теорема неверна сама по себе (см.
        // collectGarbage). Зато там есть отбор посильнее: «верно и без условия»
        // отсеивает целыми сотнями, и всё дожившее уже про посылку. Поэтому
        // берём первое попавшееся из перемешанного.
        if (last.hypothesis) {
          if (cand.length) picked = { ...cand[0], onto: [] };
        } else
        for (const { f, i } of cand) {
          if (luckyStop) break;
          if (++looked > 60) break;
          // Обобщение одного факта синхронно и небыстро. Уступаем кадр раз в
          // пять фактов: иначе «прекратить» ждёт конца всей проверки, а это
          // секунды.
          if (looked % 5 === 0) {
            say(`<p class="working">попытка ${attempt}: проверяю факт ${looked} из ${nice(pool)}…</p>`);
            await new Promise(r => setTimeout(r, 0));
            if (luckyStop) break;
          }
          let g = null;
          try {
            g = generalizeFact(f, last.world, {
              steps: last.steps, visible: last.visible, K: 8, seed: 909090,
            });
          } catch { continue; }
          // Отсеивает только ослабление ДО ВСЕЙ ПЛОСКОСТИ: тогда условие и
          // правда пустое. Обобщение до носителя («верно для любой точки BC»)
          // задачу не портит — оно её усиливает, и о нём просто сообщается.
          if (g.wider.length) continue;
          picked = { f, i, onto: g.onto ?? [] };
          break;
        }
        if (picked) {
          const text = inUiLanguage(() => problemText(picked.f, last.world,
            { conditions: conditionsOf(last.steps, last.kindOf),
              hypothesis: last.hypothesis?.conds,
          locus: last.locus ? { moving: last.locus.moving, along: last.locus.along, fixed: picked.f?.locus?.fixed } : null }));
          say(`<p class="gen-stat">случайная задача — попытка ${attempt},`
            + ` мир ${nice(cap)}, годных фактов ${nice(pool)}:</p>`
            + `<ol class="gen-facts"><li data-fact="${picked.i}">`
            + `<span class="gen-weight">${substance(picked.f)}</span> `
            + withSubscripts(escapeHtml(statement(picked.f, last.world)))
            + ` <button type="button" class="chip draw" data-fact="${picked.i}">нарисовать</button>`
            + ` <button type="button" class="chip statement" data-fact="${picked.i}">условие</button>`
            + ` <button type="button" class="chip save" data-fact="${picked.i}">скачать</button>`
            + ` <button type="button" class="chip wider" data-fact="${picked.i}">обобщить</button>`
            + `</li></ol>`
            + `<div class="gen-statement"><pre>${withSubscripts(escapeHtml(text))}</pre></div>`
            + '<p class="gen-hint">условие ослабить нельзя: каждая гипотеза существенна,'
            + ' и все данные участвуют.</p>'
            + (picked.onto.length
              ? '<p class="gen-hint">но обобщение есть: теорема верна для любой точки носителя —'
                + picked.onto.map(r => ` ${escapeHtml(r.text)}`).join(';')
                + '. Условие от этого не рушится, задача остаётся.</p>'
              : ''));
          return;
        }
        say(`<p class="working">попытка ${attempt} (мир ${nice(cap)}`
          + (attempt === 1 ? '' : ', случайный отбор наборов')
          + `): найдено ${nice(last?.kept?.length ?? 0)} фактов, годных ${nice(pool)},`
          + ' ни один не устоял — пробую дальше…</p>');
        await new Promise(r => setTimeout(r, 30));
      }
      say(`<p class="gen-hint">поиск прекращён на ${attempt}-й попытке</p>`);
    } catch (e) {
      say(`<p class="warn">не получилось: ${escapeHtml(e.message)}</p>`);
    } finally {
      delete lucky.dataset.busy;
      lucky.disabled = false;
      lucky.textContent = was;
    }
  });
  document.getElementById('gen-help').addEventListener('click', () => {
    say('<p class="gen-hint">Число слева от факта — сколько в нём содержания: на сколько'
      + ' объектов больше необходимого. У прямой это точки сверх двух, у окружности — сверх трёх.</p>'
      + '<p class="gen-hint">Считается ЧИСЛЕННО: конструкция раскладывается в несколько'
      + ' независимых конфигураций, и утверждение принимается, только если верно во всех.'
      + ' Порог взят щедрый нарочно — так не теряется ни одна верная теорема, — а от ложных'
      + ' защищает не порог, а согласие всех конфигураций сразу. Выдача потом перепроверяется'
      + ' ещё раз, на свежих конфигурациях с другим зерном.</p>'
      + '<p class="gen-hint">Что считается очевидным: следствия самого построения'
      + ' (сторона касается вписанной окружности — это не теорема, а то, как её строили),'
      + ' то, что берётся счётом углов, копии и повторы по симметрии условия. А вот то, что'
      + ' доказывается подобием, очевидным НЕ считается и остаётся в выдаче.</p>'
      + '<p class="gen-hint">Кнопка «хватит» обрывает текущий этап и переходит к следующему;'
      + ' найденное при этом остаётся. Нажмёте ещё раз — оборвётся и следующий.</p>');
  });

  // Подписи под каждой галочкой мелким шрифтом занимали половину панели.
  // Прячем их за знаком вопроса у соответствующей строки: пояснение нужно
  // один раз, а мешает оно постоянно.
  markLimits();
  hideHints();
  restore();
  forecast();
}
