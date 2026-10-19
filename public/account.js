import { CONFIG } from './config.js';

// УЧЁТНЫЕ ЗАПИСИ, ПРАВА И ЧАТ.
//
// Приложение считает всё в браузере и в сервере не нуждается — поэтому вся
// работа с ним собрана здесь, отдельным модулем, и вызывается по желанию. Если
// сети нет или библиотека не загрузилась, остальное приложение обязано
// работать как прежде: ошибки отсюда наружу не выходят.
//
// ЧТО ДАЁТ ВХОД. Бариканатор и генератор теорем открываются КАЖДЫЙ ДО СВОЕГО
// ЧИСЛА — по оплате или рукой администратора. Пока срок не наступил или уже
// вышел, кнопок этих движков просто нет.
//
// Срок, а не флаг: подписка обязана кончаться сама, и база хранит ровно одну
// величину — «открыто до». Бессрочно выданное записано как 'infinity' и
// сравнивается с датами без всякого особого случая.
//
// Сравнение сроков здесь — для интерфейса: чтобы он не предлагал того, чего
// не дадут. Выдачу решает сервер.
//
// ЭТОТ ФАЙЛ РАЗДАЁТСЯ КАЖДОМУ ПОСЕТИТЕЛЮ. Разбор устройства — в README
// приватного репозитория: что уезжает в браузер, то читают все.
//
// ВЕРСИЯ «ОДИН ФАЙЛ» живёт без всего этого: сети там нет, спрашивать некого,
// и собирается она только с Компланатором.

let supa = null;          // клиент базы, появляется после первой удачной загрузки
let session = null;       // текущая сессия или null
let me = null;            // строка profiles текущего человека
let chatSub = null;       // подписка на новые сообщения
let recoveryMode = false; // пришли по ссылке «забыл пароль»
let changingPassword = false;
const listeners = new Set();

// ---- мелочи интерфейса -----------------------------------------------------

const el = (tag, cls, text) => {
  const node = document.createElement(tag);
  if (cls) node.className = cls;
  if (text !== undefined) node.textContent = text;
  return node;
};

const chip = (text, onClick, cls = '') => {
  const b = el('button', `chip ${cls}`.trim(), text);
  b.type = 'button';
  b.addEventListener('click', onClick);
  return b;
};

const field = (type, placeholder, value = '') => {
  const i = document.createElement('input');
  i.type = type;
  i.placeholder = placeholder;
  i.value = value;
  i.autocomplete = type === 'password' ? 'current-password' : 'email';
  return i;
};

// Время по-человечески: в чате важно «когда относительно сейчас».
function when(iso) {
  const t = new Date(iso), now = new Date();
  const mins = Math.round((now - t) / 60000);
  if (mins < 1) return 'только что';
  if (mins < 60) return `${mins} мин назад`;
  const sameDay = t.toDateString() === now.toDateString();
  const hhmm = t.toLocaleTimeString('ru', { hour: '2-digit', minute: '2-digit' });
  if (sameDay) return hhmm;
  return `${t.toLocaleDateString('ru', { day: 'numeric', month: 'short' })}, ${hhmm}`;
}

// ---- связь с базой ---------------------------------------------------------

async function connect() {
  if (supa) return supa;
  const { createClient } = await import(/* @vite-ignore */ CONFIG.lib);
  supa = createClient(CONFIG.url, CONFIG.key, {
    auth: { persistSession: true, autoRefreshToken: true },
  });
  return supa;
}

async function loadMe() {
  if (!session) { me = null; return null; }
  const { data, error } = await supa.from('profiles').select('*').eq('id', session.user.id).single();
  me = error ? null : data;
  // «Был на сайте» — для статистики администратора. Промах не беда.
  supa.rpc('touch_seen').then(() => {}, () => {});
  return me;
}

// ---- сроки доступа --------------------------------------------------------

// Бессрочное приходит из базы СТРОКОЙ «infinity»: это настоящее значение
// timestamptz, но Date его не разбирает — new Date('infinity') даёт Invalid
// Date, которое молча проваливает любое сравнение. Поэтому особый случай
// проверяется ПЕРВЫМ, до разбора даты.
const FOREVER = 'infinity';

const openUntil = v => !!v && (v === FOREVER || Date.parse(v) > Date.now());

// Срок по-человечески. Год пишем только чужой: «до 14 марта» читается легче,
// чем «до 14.03.2027», а когда год и правда другой — его надо видеть.
export function untilText(v) {
  if (!v) return 'закрыто';
  if (v === FOREVER) return 'бессрочно';
  const t = new Date(v);
  if (Number.isNaN(t.getTime())) return 'закрыто';
  const opts = { day: 'numeric', month: 'long' };
  if (t.getFullYear() !== new Date().getFullYear()) opts.year = 'numeric';
  return `${openUntil(v) ? 'до' : 'кончилось'} ${t.toLocaleDateString('ru', opts)}`;
}

// Кто что может.
//
// ПОКА МОДУЛЬ НЕ ПОДНЯЛСЯ — ЗАКРЫТО. Раньше здесь было открыто: считалось, что
// запрет, который нельзя снять входом, — просто поломанное приложение. Но на
// сайте «модуль не поднялся» значит всего лишь «библиотека ещё летит» или «её
// загрузку заблокировали», и открывать по этому поводу платные движки нельзя:
// иначе блокировщик esm.sh оказывается бесплатным ключом ко всему. А версия
// «один файл» сюда больше не приходит — она до account.js не доходит вовсе
// (см. setupAccountModule в app.js).
//
// known значит не «разрешено», а «знаем ли уже»: интерфейсу это нужно, чтобы
// не мигать кнопками, пока база не ответила.
export function rights() {
  if (!supa) {
    return {
      known: false, bary: false, gen: false, admin: false, signedIn: false,
      baryUntil: null, genUntil: null,
    };
  }
  return {
    known: true,
    bary: openUntil(me?.bary_until),
    gen: openUntil(me?.gen_until),
    // Сырые значения, как пришли из базы: показывать их — дело untilText.
    baryUntil: me?.bary_until ?? null,
    genUntil: me?.gen_until ?? null,
    admin: me?.role === 'admin',
    signedIn: !!session,
  };
}

// ---- платные модули -------------------------------------------------------
//
// Разбор устройства — в README приватного репозитория. Здесь только вызов:
// этот файл раздаётся каждому, и объяснять в нём нечего.
const PAID = { bary: 'bary.js', gen: 'gen.js', export: 'export.js' };

export async function paidModule(what) {
  const file = PAID[what];
  if (!file) throw new Error(`неизвестный платный модуль: ${what}`);
  await connect();
  if (!session) throw new Error('нужно войти');

  const { data, error } = await supa.storage.from('paid').download(file);
  // Отказ политики приходит сюда же, и это нормальный ответ, а не поломка:
  // значит срок закрыт. Текст берём общий — человеку всё равно, чем именно
  // ответило хранилище.
  if (error) throw new Error(ruError(error));

  const url = URL.createObjectURL(new Blob([await data.text()], { type: 'text/javascript' }));
  try {
    return await import(/* @vite-ignore */ url);
  } finally {
    // Ссылку надо отпустить: модуль уже разобран и живёт сам по себе, а blob
    // иначе держал бы эти мегабайты до перезагрузки страницы.
    URL.revokeObjectURL(url);
  }
}

export function onChange(fn) { listeners.add(fn); return () => listeners.delete(fn); }
const changed = () => { for (const fn of listeners) { try { fn(rights()); } catch { /* не наше дело */ } } };

// ---- вход и выход ----------------------------------------------------------

function authForm(box, note) {
  const wrap = el('div', 'acc-form');
  const email = field('email', 'почта');
  const pass = field('password', 'пароль');
  pass.autocomplete = 'current-password';
  const say = el('div', 'acc-note');

  const run = async (how) => {
    say.className = 'acc-note';
    say.textContent = 'минуту…';
    try {
      const fn = how === 'up' ? 'signUp' : 'signInWithPassword';
      const { data, error } = await supa.auth[fn]({ email: email.value.trim(), password: pass.value });
      if (error) throw error;
      // При открытой регистрации без подтверждения почты сессия приходит сразу.
      if (!data.session) {
        say.textContent = 'проверьте почту: нужно подтвердить адрес';
        return;
      }
      session = data.session;
      await loadMe();
      render();
      changed();
    } catch (e) {
      say.className = 'acc-note bad';
      say.textContent = ruError(e);
    }
  };

  // ЗАБЫТЫЙ ПАРОЛЬ — НЕ МЕЛОЧЬ ДЛЯ ОТКРЫТОГО САЙТА.
  //
  // Регистрация свободная, входят по почте и паролю, и без восстановления
  // человек, забывший пароль, теряет учётную запись насовсем: ни админ, ни я
  // чужой пароль не видим и поставить новый не можем.
  const forgot = chip('забыл пароль', async () => {
    const who = email.value.trim();
    if (!who) { say.className = 'acc-note bad'; say.textContent = 'впишите почту'; return; }
    say.className = 'acc-note';
    say.textContent = 'отправляю письмо…';
    try {
      const { error } = await supa.auth.resetPasswordForEmail(who, {
        redirectTo: location.origin + location.pathname,
      });
      if (error) throw error;
      say.textContent = 'письмо отправлено: перейдите по ссылке из него и задайте новый пароль';
    } catch (e) {
      say.className = 'acc-note bad';
      say.textContent = ruError(e);
    }
  }, 'canon');

  const bar = el('div', 'console-bar');
  bar.append(chip('войти', () => run('in')), chip('зарегистрироваться', () => run('up')), forgot);
  wrap.append(note, email, pass, bar, say);
  box.append(wrap);
}

// ---- новый пароль -----------------------------------------------------------
//
// Одна и та же форма служит двум случаям: человек пришёл по ссылке из письма
// (сессия уже есть, но пароля он не помнит) и человек просто хочет сменить
// пароль. Разница только в подписи.
function passwordForm(box, { recovery = false } = {}) {
  const wrap = el('div', 'acc-form');
  const pass = field('password', 'новый пароль, не короче шести знаков');
  pass.autocomplete = 'new-password';
  const say = el('div', 'acc-note');
  const set = chip('сохранить пароль', async () => {
    if (pass.value.length < 6) {
      say.className = 'acc-note bad';
      say.textContent = 'пароль короче шести знаков';
      return;
    }
    say.className = 'acc-note';
    say.textContent = 'минуту…';
    try {
      const { error } = await supa.auth.updateUser({ password: pass.value });
      if (error) throw error;
      recoveryMode = false;
      changingPassword = false;
      render();
    } catch (e) {
      say.className = 'acc-note bad';
      say.textContent = ruError(e);
    }
  });
  const bar = el('div', 'console-bar');
  bar.append(set);
  if (!recovery) {
    bar.append(chip('отмена', () => { changingPassword = false; render(); }, 'canon'));
  }
  wrap.append(el('div', 'gen-hint', recovery
    ? 'Вы перешли по ссылке из письма. Задайте новый пароль — и войдёте с ним.'
    : 'Новый пароль вступит в силу сразу, перезаходить не нужно.'), pass, bar, say);
  box.append(wrap);
}

// Сообщения службы приходят по-английски и не всегда понятны; переводим те,
// что встречаются на деле, остальное показываем как есть — врать не надо.
function ruError(e) {
  const t = String(e?.message ?? e);
  if (/Invalid login credentials/i.test(t)) return 'не подходит: проверьте почту и пароль';
  if (/User already registered/i.test(t)) return 'такая почта уже зарегистрирована — войдите';
  if (/Password should be at least/i.test(t)) return 'пароль короче шести знаков';
  if (/valid email/i.test(t)) return 'почта написана неправильно';
  if (/rate limit|too many/i.test(t)) return 'слишком часто — подождите минуту';
  if (/Failed to fetch|NetworkError/i.test(t)) return 'нет связи с сервером';
  return t;
}

// ---- блок «учётная запись» --------------------------------------------------

function render() {
  const box = document.getElementById('account-body');
  if (!box) return;
  box.textContent = '';

  // Пришли по ссылке из письма: сессия есть, но первым делом нужен новый
  // пароль, а не список прав.
  if (session && (recoveryMode || changingPassword)) {
    passwordForm(box, { recovery: recoveryMode });
    return;
  }
  if (!session) {
    // Текст называет ЦЕНУ прямо здесь, на экране входа. Раньше тут стояло
    // «которые открывает администратор» — это осталось от времён, когда права
    // раздавались рукой; человек заводил запись и ждал, пока ему откроют.
    // Теперь он может купить сам, и узнать об этом должен до регистрации, а не
    // после.
    authForm(box, el('div', 'gen-hint',
      'Вход нужен для чата и для платных движков: Бариканатора и генератора '
      + 'теорем — по 150 ₽ за месяц каждый. Компланатор бесплатен и работает '
      + 'всем, даже без входа.'));
    return;
  }

  const head = el('div', 'acc-head');
  head.append(el('b', '', me?.name || session.user.email));
  if (me?.role === 'admin') head.append(el('span', 'acc-tag', 'администратор'));
  box.append(head);

  // ЧТО ОТКРЫТО И ДО КАКОГО ЧИСЛА. Срок показывается рядом с названием, а не
  // где-то в настройках: человек, у которого подписка кончается в пятницу,
  // должен узнать об этом, просто заглянув в кабинет.
  const r = rights();
  const what = [
    ['Компланатор', true, FOREVER],
    ['Бариканатор', r.bary, r.baryUntil],
    ['генератор теорем', r.gen, r.genUntil],
  ];
  const list = el('div', 'acc-note');
  for (const [name, ok, upto] of what) {
    const line = el('div', '', `${ok ? '✓' : '—'} ${name}`);
    // У бессрочного срока не пишем: «Компланатор бессрочно» — шум, открытое
    // навсегда и так читается галочкой.
    if (upto !== FOREVER) line.append(el('span', 'acc-tag', untilText(upto)));
    list.append(line);
  }
  box.append(list);

  // ПОКУПКА. Кнопка стоит у того движка, который закрыт, а не общим списком:
  // так видно, за что именно платишь.
  //
  // Сумму и срок решает сервер (см. функцию pay): браузер присылает только,
  // какой движок покупают. Иначе цену прислали бы равной рублю.
  const buy = (label, what) => {
    const b = chip(`купить ${label} — 150 ₽ на месяц`, async () => {
      b.disabled = true;
      const was = b.textContent;
      b.textContent = 'минуту…';
      try {
        const { data, error } = await supa.functions.invoke('pay', { body: { what } });
        if (error) throw error;
        if (!data?.url) throw new Error('касса не дала ссылки');
        // Уводим на страницу оплаты. Вернётся человек уже на сайт.
        location.href = data.url;
      } catch (e) {
        b.disabled = false;
        b.textContent = was;
        alert(ruError(e));
      }
    });
    return b;
  };

  if (!r.bary || !r.gen) {
    const row = el('div', 'console-bar');
    if (!r.bary) row.append(buy('Бариканатор', 'bary'));
    if (!r.gen) row.append(buy('генератор', 'gen'));
    box.append(row);
    box.append(el('div', 'gen-hint',
      'Оплата через ЮKassa. Доступ открывается сам, обычно за минуту.'));
  }

  const bar = el('div', 'console-bar');
  bar.append(chip('сменить пароль', () => { changingPassword = true; render(); }, 'canon'));
  bar.append(chip('выйти', async () => {
    await supa.auth.signOut();
    session = null; me = null;
    render(); changed(); renderChat();
  }));
  box.append(bar);

  if (me?.role === 'admin') adminPanel(box);
}

// ---- панель администратора --------------------------------------------------

async function adminPanel(box) {
  const wrap = el('details', 'why admin-block');
  const sum = el('summary', '', 'люди и права');
  wrap.append(sum);
  const body = el('div');
  wrap.append(body);
  box.append(wrap);

  wrap.addEventListener('toggle', () => { if (wrap.open) fill(); }, { once: false });

  async function fill() {
    body.textContent = 'читаю…';
    const [{ data: people, error }, { data: stats }] = await Promise.all([
      supa.from('profiles').select('*').order('created_at', { ascending: false }),
      supa.rpc('admin_stats'),
    ]);
    body.textContent = '';
    if (error) { body.append(el('div', 'acc-note bad', ruError(error))); return; }

    if (stats) {
      const s = stats;
      body.append(el('div', 'acc-note',
        `людей ${s.people} (за неделю +${s.new_week}), администраторов ${s.admins}; `
        // Открыто всего и из них по сроку: второе число — подписчики, первое
        // включает и выданное админом бессрочно.
        + `Бариканатор открыт ${s.with_bary} (по сроку ${s.paid_bary}), `
        + `генератор ${s.with_gen} (по сроку ${s.paid_gen}); `
        + `кончается на неделе у ${s.ending_week}; `
        + `заходили за сутки ${s.active_day}, за неделю ${s.active_week}; `
        + `тем ${s.topics}, сообщений ${s.messages} (за неделю ${s.messages_week})`));
    }

    const table = el('div', 'acc-people');
    for (const p of people ?? []) {
      const row = el('div', 'acc-person');
      const who = el('span', 'acc-who', p.name || p.id.slice(0, 8));
      if (p.role === 'admin') who.append(el('span', 'acc-tag', 'админ'));
      row.append(who);

      // ПРАВО ВЫДАЁТСЯ СРОКОМ, И ОДНОЙ КНОПКОЙ-ПЕРЕКЛЮЧАТЕЛЕМ ЭТО НЕ ВЫРАЗИТЬ.
      //
      // Раньше стоял флаг, и нажатие его переворачивало. Теперь состояний три
      // — закрыто, открыто до числа, открыто бессрочно, — и переключатель по
      // кругу заставлял бы угадывать, что получится. Поэтому кнопки называют
      // не состояние, а ДЕЙСТВИЕ, а состояние написано рядом словами.
      //
      // «+мес» идёт через extend_access, а не через update: месяцы надо
      // складывать от большего из «сейчас» и «открыто до», и этот счёт живёт
      // в базе одной копией — тем же путём пойдёт потом и вебхук оплаты.
      const access = (label, key) => {
        const col = `${key}_until`;
        const wrap = el('span', 'acc-access');
        const state = el('span', 'acc-tag');
        const show = () => { state.textContent = untilText(p[col]); };

        const act = (text, title, run) => {
          const b = chip(text, async () => {
            const buttons = [...wrap.querySelectorAll('button')];
            for (const x of buttons) x.disabled = true;
            try {
              p[col] = await run();
              show();
              // Право могло измениться у меня самого — тогда панель
              // перестроится, и закрытый себе движок исчезнет сразу.
              if (p.id === session.user.id) { await loadMe(); render(); changed(); }
            } catch (e) {
              alert(ruError(e));
            } finally {
              for (const x of buttons) x.disabled = false;
            }
          });
          b.title = `${title} — ${label}`;
          return b;
        };

        show();
        wrap.append(
          el('span', 'acc-what', label), state,
          act('+мес', 'добавить месяц', async () => {
            const { data, error: err } = await supa.rpc('extend_access',
              { who: p.id, what: key, span: '1 month' });
            if (err) throw err;
            return data;
          }),
          act('∞', 'открыть бессрочно', async () => {
            const { error: err } = await supa.from('profiles')
              .update({ [col]: 'infinity' }).eq('id', p.id);
            if (err) throw err;
            return 'infinity';
          }),
          act('×', 'закрыть', async () => {
            const { error: err } = await supa.from('profiles')
              .update({ [col]: null }).eq('id', p.id);
            if (err) throw err;
            return null;
          }),
        );
        return wrap;
      };
      row.append(access('Бариканатор', 'bary'), access('генератор', 'gen'));

      const rank = chip(p.role === 'admin' ? 'разжаловать' : 'в админы', async () => {
        rank.disabled = true;
        const role = p.role === 'admin' ? 'user' : 'admin';
        const { error: err } = await supa.from('profiles').update({ role }).eq('id', p.id);
        rank.disabled = false;
        if (err) { alert(ruError(err)); return; }
        fill();
      });
      row.append(rank);
      table.append(row);
    }
    body.append(table);
  }
}

// ---- чат --------------------------------------------------------------------

let currentTopic = null;

async function renderChat() {
  const block = document.getElementById('chat-block');
  const box = document.getElementById('chat-body');
  if (!box) return;
  box.textContent = '';
  if (!session) {
    block.hidden = true;
    return;
  }
  block.hidden = false;

  const { data: topics, error } = await supa.from('topics')
    .select('*').order('created_at', { ascending: false });
  if (error) { box.append(el('div', 'acc-note bad', ruError(error))); return; }

  const bar = el('div', 'chat-topics');
  for (const t of topics ?? []) {
    const b = chip(t.title, () => { currentTopic = t.id; renderChat(); });
    b.setAttribute('aria-pressed', String(currentTopic === t.id));
    if (me?.role === 'admin') {
      b.title = 'тема (удалить — долгим нажатием или правой кнопкой)';
      b.addEventListener('contextmenu', async (ev) => {
        ev.preventDefault();
        if (!confirm(`Удалить тему «${t.title}» вместе со всеми сообщениями?`)) return;
        await supa.from('topics').delete().eq('id', t.id);
        if (currentTopic === t.id) currentTopic = null;
        renderChat();
      });
    }
    bar.append(b);
  }
  if (me?.role === 'admin') {
    bar.append(chip('+ тема', async () => {
      const title = prompt('Название темы');
      if (!title?.trim()) return;
      const { error: err } = await supa.from('topics').insert({ title: title.trim(), created_by: session.user.id });
      if (err) { alert(ruError(err)); return; }
      renderChat();
    }, 'engine'));
  }
  box.append(bar);

  if (!topics?.length) {
    box.append(el('div', 'gen-hint', me?.role === 'admin'
      ? 'Тем пока нет. Заведите первую — кнопкой «+ тема».'
      : 'Тем пока нет: их заводит администратор.'));
    return;
  }
  if (currentTopic === null) currentTopic = topics[0].id;

  const list = el('div', 'chat-list');
  box.append(list);
  await fillMessages(list);

  const write = document.createElement('textarea');
  write.rows = 2;
  write.placeholder = 'написать в тему';
  const send = chip('отправить', async () => {
    const body = write.value.trim();
    if (!body) return;
    send.disabled = true;
    const { error: err } = await supa.from('messages')
      .insert({ topic_id: currentTopic, author: session.user.id, body });
    send.disabled = false;
    if (err) { alert(ruError(err)); return; }
    write.value = '';
    fillMessages(list);
  });
  // Enter отправляет, Shift+Enter переводит строку: в чате так ждут.
  write.addEventListener('keydown', (ev) => {
    if (ev.key === 'Enter' && !ev.shiftKey) { ev.preventDefault(); send.click(); }
  });
  const bar2 = el('div', 'console-bar');
  bar2.append(send);
  box.append(write, bar2);

  // Новые сообщения приходят сами — иначе чат приходится перезагружать.
  chatSub?.unsubscribe?.();
  chatSub = supa.channel('messages-live')
    .on('postgres_changes', { event: '*', schema: 'public', table: 'messages' },
      () => fillMessages(list))
    .subscribe();
}

async function fillMessages(list) {
  const { data, error } = await supa.from('messages')
    .select('id, body, created_at, author, profiles(name)')
    .eq('topic_id', currentTopic)
    .order('created_at', { ascending: true })
    .limit(200);
  list.textContent = '';
  if (error) { list.append(el('div', 'acc-note bad', ruError(error))); return; }
  if (!data?.length) { list.append(el('div', 'gen-hint', 'Пока пусто. Напишите первым.')); return; }
  for (const m of data) {
    const row = el('div', 'chat-msg');
    const head = el('div', 'chat-who');
    head.append(el('b', '', m.profiles?.name || 'кто-то'), el('span', 'acc-note', when(m.created_at)));
    if (m.author === session.user.id || me?.role === 'admin') {
      head.append(chip('удалить', async () => {
        if (!confirm('Удалить сообщение?')) return;
        await supa.from('messages').delete().eq('id', m.id);
        fillMessages(list);
      }, 'canon'));
    }
    row.append(head, el('div', 'chat-body-text', m.body));
    list.append(row);
  }
  list.scrollTop = list.scrollHeight;
}

// ---- запуск -----------------------------------------------------------------

export async function setupAccount() {
  const block = document.getElementById('account-block');
  if (!block) return;
  // Локальный файл сетью не располагает: молча не показываемся.
  if (location.protocol === 'file:') return;
  try {
    await connect();
    const { data } = await supa.auth.getSession();
    session = data.session ?? null;
    if (session) await loadMe();
  } catch {
    return;                      // не загрузилось — приложение работает как прежде
  }
  block.hidden = false;
  render();
  renderChat();
  changed();
  supa.auth.onAuthStateChange(async (event, s) => {
    session = s ?? null;
    // Переход по ссылке из письма приходит отдельным событием: сессия выдана,
    // но пароля человек не знает, и показывать ему права вместо формы — значит
    // оставить его без входа в следующий раз.
    if (event === 'PASSWORD_RECOVERY') {
      recoveryMode = true;
      changingPassword = false;
      const block = document.getElementById('account-block');
      if (block) block.open = true;
    }
    if (session) await loadMe(); else me = null;
    render(); renderChat(); changed();
  });
}
