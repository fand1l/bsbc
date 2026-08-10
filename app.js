/* =========================================================================
   КРЕСАЛО К1 — розбирання на скролі.

   Правила, за якими написано цей файл:
   • обробник скролу нічого не рендерить — уся робота в requestAnimationFrame;
   • прогрес читається з getBoundingClientRect() доріжки один раз на кадр,
     тому жодні кешовані offsetTop не можуть застаріти після завантаження
     шрифтів, зміни масштабу чи повороту екрана;
   • згладжування — експоненційне з поправкою на dt, з праймом на першому
     кадрі й після будь-якого стрибка, щоб не було ривка на старті;
   • DOM пишеться тільки коли активний шар змінився, а не щокадру;
   • жоден шар не рушає вниз, поки корпус під ним не звільнив дорогу;
   • якщо three.js або WebGL недоступні — та сама змінна прогресу керує
     плоскою схемою, і сторінка лишається робочою.
   ========================================================================= */
(function () {
  'use strict';

  /* --- дані шарів -------------------------------------------------------
     seat — де шар сидить у зібраному пристрої (світові одиниці, 1 ≈ 37 мм)
     ms/md — коли починається і скільки триває його рух
     cs — коли перемикається його картка
     Корпус рушає раніше за акумулятор і радіатор навмисне: він їх тримає,
     і поки він на місці, вниз їм нема куди. Саме через зворотний порядок
     деталі раніше проходили крізь дно. */
  var LAYERS = [
    { no: '01', name: 'екран',      seat:  0.222, half: 0.035, travel:  3.30, ease: 3, ms: 0.06, md: 0.18, cs: 0.06, dx:  0.10, dz: -0.04, rz:  0.020, rx: 0 },
    { no: '02', name: 'клавіатура', seat:  0.225, half: 0.040, travel:  2.05, ease: 4, ms: 0.17, md: 0.18, cs: 0.17, dx: -0.08, dz:  0.05, rz: -0.015, rx: 0 },
    { no: '03', name: 'плата',      seat:  0.150, half: 0.045, travel:  0.90, ease: 3, ms: 0.28, md: 0.18, cs: 0.28, dx:  0.05, dz:  0.06, rz: 0,      rx:  0.012 },
    { no: '04', name: 'акумулятор', seat:  0.030, half: 0.085, travel: -0.55, ease: 2, ms: 0.46, md: 0.22, cs: 0.46, dx:  0.07, dz: -0.03, rz: 0,      rx: -0.010 },
    { no: '05', name: 'радіатор',   seat: -0.130, half: 0.075, travel: -1.85, ease: 3, ms: 0.40, md: 0.26, cs: 0.54, dx: -0.05, dz:  0.04, rz:  0.014, rx: 0 },
    { no: '06', name: 'корпус',     seat: -0.030, half: 0.245, travel: -3.10, ease: 2, ms: 0.33, md: 0.30, cs: 0.64, dx:  0,    dz:  0,    rz: 0,      rx:  0.008 }
  ];

  // зазор між сусідніми шарами в зібраному пристрої; від'ємний там, де
  // деталі вкладені одна в одну (стінки корпусу охоплюють решту)
  var GAP0 = [];
  var SCREW_A = 0.015, SCREW_B = 0.060;   // гвинти викручуються перед усім
  var HOLD_A  = 0.70,  HOLD_B  = 0.86;    // витримка: розібраний пристрій стоїть
  var COLLAPSE = 0.86;                    // далі складається назад
  var SMOOTH_K = 12;

  /* --- вузли ------------------------------------------------------------ */
  var track  = document.getElementById('track');
  var stage  = document.getElementById('stage');
  var vis    = document.getElementById('vis');
  var canvas = document.getElementById('cv');
  var flat   = document.getElementById('flat');
  var lead   = document.getElementById('lead');
  var leadLine = document.getElementById('lead-line');
  var leadRing = document.getElementById('lead-ring');
  var leadDot  = document.getElementById('lead-dot');
  var cardsBox = document.getElementById('cards');
  var cards  = Array.prototype.slice.call(cardsBox.querySelectorAll('.card'));
  var flats  = Array.prototype.slice.call(flat.querySelectorAll('.flat__p'));
  var screwsBox = document.getElementById('screws');
  var themeBtn  = document.getElementById('theme');
  var fxBtn     = document.getElementById('fx');
  var fxVal     = document.getElementById('fxval');
  var ann    = document.getElementById('ann');
  var root   = document.documentElement;

  /* --- стан ------------------------------------------------------------- */
  var motionMQ = window.matchMedia('(prefers-reduced-motion: reduce)');
  var themeMQ  = window.matchMedia('(prefers-color-scheme: dark)');
  var reduced = motionMQ.matches;
  var smoothed = 0, primed = false;
  var lastIndex = -1, lastFrame = 0, rafId = 0, running = false, dirty = true;
  var us = [0, 0, 0, 0, 0, 0];
  var ys = [0, 0, 0, 0, 0, 0];
  var three = null;
  var visW = 0, visH = 0, visOX = 0, visOY = 0, cardX = 0, cardAnchorY = 0;
  var leadOn = false, spread = 1;
  var annTimer = 0, lastDrawn = -1, staticMode = false;
  var stickyPx = 0, denom = 0;
  var dims = [1, 0.4, 0.4, 0.4, 0.4, 0.4], dimsPrev = [-1, -1, -1, -1, -1, -1];
  var fxOn = true, fxManual = false;
  var perfN = 0, perfSum = 0, perfSteps = 0, dprCapNow = 2;

  for (var gi = 0; gi < 5; gi++) {
    GAP0.push((LAYERS[gi].seat - LAYERS[gi].half) - (LAYERS[gi + 1].seat + LAYERS[gi + 1].half));
  }

  function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }
  function easeOut(u, k) { return 1 - Math.pow(1 - u, k); }
  function smoothstep(a, b, x) { var t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); }
  function win(a, b, x) { return clamp((x - a) / (b - a), 0, 1); }

  /* --- 1. Тема ---------------------------------------------------------- */
  function isDark() {
    var t = root.dataset.theme;
    return t ? t === 'dark' : themeMQ.matches;
  }

  function labelTheme() {
    themeBtn.setAttribute('aria-label',
      isDark() ? 'Перемкнути на світлу тему' : 'Перемкнути на темну тему');
  }

  function onTheme() {
    labelTheme();
    if (three) {
      var dark = isDark();
      three.renderer.toneMappingExposure = dark ? 0.92 : 1.12;
      three.scene.environmentIntensity = dark ? 0.7 : 1.0;
      three.key.intensity = dark ? 1.1 : 1.8;
      three.rim.intensity = dark ? 0.5 : 0.7;
      three.hemi.intensity = dark ? 0.35 : 0.6;
    }
    dirty = true;
    wake();
  }

  themeBtn.addEventListener('click', function () {
    var next = isDark() ? 'light' : 'dark';
    root.dataset.theme = next;
    try { localStorage.setItem('k1-theme', next); } catch (e) { /* приватний режим */ }
    onTheme();
  });

  themeMQ.addEventListener('change', function () { if (!root.dataset.theme) onTheme(); });

  /* --- 1a. Якість проти швидкості --------------------------------------
     Тумблер керує трьома речами одразу: світінням екрана, віньєткою й
     роздільною здатністю рендера. Ручний вибір вимикає автоматичне
     зниження якості — якщо людина свідомо просить «якість», сторінка не
     має мовчки відбирати її назад. */
  try {
    var savedFx = localStorage.getItem('k1-fx');
    if (savedFx === 'on' || savedFx === 'off') { fxOn = savedFx === 'on'; fxManual = true; }
  } catch (e) { /* приватний режим */ }

  function applyFx() {
    root.classList.toggle('fx-off', !fxOn);
    fxBtn.setAttribute('aria-checked', fxOn ? 'true' : 'false');
    fxVal.textContent = fxOn ? 'якість' : 'швидкість';
    if (three) {
      if (three.glow) three.glow.visible = fxOn;
      for (var i = 0; i < three.shadows.length; i++) {
        if (!fxOn) three.shadows[i].mesh.visible = false;
      }
      dprCapNow = fxOn ? (window.innerWidth < 768 ? 1.5 : 2) : 1;
      three.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, dprCapNow));
      three.renderer.setSize(visW, visH, false);
    }
    dirty = true;
    wake();
  }

  fxBtn.addEventListener('click', function () {
    fxOn = !fxOn;
    fxManual = true;
    perfSteps = 2;               // людина вирішила сама — більше не втручаємось
    try { localStorage.setItem('k1-fx', fxOn ? 'on' : 'off'); } catch (e) { /* приватний режим */ }
    applyFx();
  });

  /* --- 2. Гвинти-індикатори -------------------------------------------- */
  var SCREW_SVG =
    '<svg class="screw__g" viewBox="0 0 24 24" width="20" height="20" aria-hidden="true" focusable="false">' +
      '<line class="screw__thread" x1="22" y1="12" x2="12" y2="12"/>' +
      '<circle class="screw__head" cx="12" cy="12" r="8"/>' +
      '<g class="screw__slot">' +
        '<rect x="6.6" y="10.8" width="10.8" height="2.4" rx="1.1"/>' +
        '<rect x="6.6" y="10.8" width="10.8" height="2.4" rx="1.1" transform="rotate(60 12 12)"/>' +
        '<rect x="6.6" y="10.8" width="10.8" height="2.4" rx="1.1" transform="rotate(120 12 12)"/>' +
      '</g>' +
    '</svg>';

  var screws = LAYERS.map(function (L, i) {
    var b = document.createElement('button');
    b.type = 'button';
    b.className = 'screw';
    b.innerHTML = '<span class="vh">Перейти до шару ' + L.no + ': ' + L.name + '</span>' + SCREW_SVG;
    b.addEventListener('click', function () { goToLayer(i); });
    screwsBox.appendChild(b);
    return b;
  });

  function goToLayer(i) {
    if (denom <= 0) return;
    var L = LAYERS[i];
    var target = i === 5 ? L.cs + 0.03 : L.ms + L.md * 0.8;
    var top = window.scrollY + track.getBoundingClientRect().top - stickyPx + target * denom;
    window.scrollTo({ top: top, behavior: 'instant' });
    primed = false;
    dirty = true;
    wake();
  }

  function readSticky() {
    var t = parseFloat(getComputedStyle(stage).top);
    stickyPx = isNaN(t) ? 0 : t;
    denom = track.offsetHeight - stage.offsetHeight;
  }

  /* --- 3. Прогрес ------------------------------------------------------- */
  function activeFrom(p) {
    var idx = 0;
    for (var i = 0; i < LAYERS.length; i++) if (p >= LAYERS[i].cs) idx = i;
    return idx;
  }

  function apply(p, dt) {
    var i, L;
    var collapse = smoothstep(COLLAPSE, 1, p);          // складання назад
    collapse = collapse * collapse;                      // прискорення до кінця

    for (i = 0; i < 6; i++) {
      L = LAYERS[i];
      us[i] = easeOut(win(L.ms, L.ms + L.md, p), L.ease) * (1 - collapse);
      ys[i] = L.seat + us[i] * L.travel * spread;
    }

    /* Запобіжник: сусідні шари ніколи не зближуються тісніше, ніж вони
       стоять у зібраному пристрої. Хореографія й так це виключає (нижні їдуть
       першими), але правило має бути в коді, а не триматися на вдало
       підібраних числах — саме через його відсутність деталі проходили
       крізь корпус. Прохід знизу вгору, щоб поправка поширювалася вище. */
    for (i = 4; i >= 0; i--) {
      var minC = ys[i + 1] + LAYERS[i + 1].half + GAP0[i] + LAYERS[i].half;
      if (ys[i] < minC) ys[i] = minC;
    }

    var idx = activeFrom(p);

    if (three) applyThree(p, collapse, dt, idx);
    else for (i = 0; i < flats.length; i++) {
      flats[i].style.setProperty('--y', (us[i] * LAYERS[i].travel * -22).toFixed(1));
    }

    for (i = 0; i < screws.length; i++) screws[i].style.setProperty('--u', us[i].toFixed(3));

    if (idx !== lastIndex) setActive(idx);
  }

  function setActive(idx) {
    lastIndex = idx;
    for (var i = 0; i < cards.length; i++) {
      var on = staticMode || i === idx;
      if (on) cards[i].setAttribute('data-on', ''); else cards[i].removeAttribute('data-on');
      cards[i].inert = !on;
      if (i === idx) screws[i].setAttribute('aria-current', 'true'); else screws[i].removeAttribute('aria-current');
    }
    clearTimeout(annTimer);
    annTimer = setTimeout(function () {
      if (cardsBox.contains(document.activeElement)) return;
      ann.textContent = 'Шар ' + LAYERS[idx].no + ' — ' + LAYERS[idx].name;
    }, 500);
  }

  /* --- 4. Цикл ---------------------------------------------------------- */
  function frame(now) {
    rafId = requestAnimationFrame(frame);

    var raw = (now - lastFrame) / 1000;
    var dt = Math.min(raw, 0.05);
    lastFrame = now;

    var t = denom > 0
      ? clamp((stickyPx - track.getBoundingClientRect().top) / denom, 0, 1)
      : 0;

    if (!primed || reduced || Math.abs(t - smoothed) > 0.25) {
      smoothed = t;
      primed = true;
    } else {
      smoothed += (t - smoothed) * (1 - Math.exp(-SMOOTH_K * dt));
    }

    if (reduced && !dirty && Math.abs(smoothed - lastDrawn) < 0.0002) return;
    lastDrawn = smoothed;
    dirty = false;

    apply(smoothed, dt);
    if (three) watchPerf(raw);
  }

  /* Реального GPU в оточенні розробки не було, тож замість здогадів про
     продуктивність сторінка міряє себе сама: якщо кадр стабільно довгий,
     вдвічі знижується роздільна здатність рендера. Вигляд лишається той
     самий — падає лише кількість пікселів, а не якість матеріалів. */
  function watchPerf(dt) {
    if (fxManual || perfSteps >= 2 || dt <= 0 || dt > 1) return;
    perfSum += dt; perfN++;
    if (perfN < 10 || perfSum < 1.2) return;
    var avg = perfSum / perfN;
    perfN = 0; perfSum = 0;
    if (avg > 0.030 && dprCapNow > 1) {
      // перший щабель: удвічі менше пікселів, вигляд той самий
      perfSteps++;
      dprCapNow = Math.max(1, dprCapNow / 2);
      three.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, dprCapNow));
      three.renderer.setSize(visW, visH, false);
    } else if (avg > 0.055) {
      // другий щабель, для зовсім слабкого заліза: прибираємо відображення.
      // Метал стане простішим, зате сторінка лишиться керованою.
      perfSteps = 2;
      three.scene.environment = null;
      for (var m = 0; m < three.mats.length; m++) {
        three.mats[m].metalness = 0.15;
        three.mats[m].roughness = 0.7;
        three.mats[m].needsUpdate = true;
      }
      three.key.intensity += 0.8;
      three.hemi.intensity += 0.5;
    } else {
      perfSteps = 2;   // швидкості вистачає, більше не міряємо
    }
  }

  function wake() {
    if (rafId) return;
    lastFrame = performance.now();
    primed = false;
    rafId = requestAnimationFrame(frame);
  }

  function sleep() {
    if (!rafId) return;
    cancelAnimationFrame(rafId);
    rafId = 0;
  }

  if ('IntersectionObserver' in window) {
    new IntersectionObserver(function (es) {
      running = es[0].isIntersecting;
      if (running && !document.hidden) wake(); else sleep();
    }, { rootMargin: '120px' }).observe(track);
  } else {
    running = true;
    wake();
  }

  document.addEventListener('visibilitychange', function () {
    if (document.hidden) sleep(); else if (running) wake();
  });

  // Обробник скролу нічого не рендерить: він лише позначає кадр брудним.
  window.addEventListener('scroll', function () { dirty = true; }, { passive: true });

  motionMQ.addEventListener('change', function (e) {
    reduced = e.matches;
    primed = false;
    dirty = true;
  });

  /* --- 5. Розміри ------------------------------------------------------- */
  var staticMQ = window.matchMedia('(max-height: 330px)');

  function measure() {
    readSticky();
    var wasStatic = staticMode;
    staticMode = staticMQ.matches;
    if (wasStatic !== staticMode) setActive(lastIndex < 0 ? 0 : lastIndex);

    var r = vis.getBoundingClientRect();
    var sr = stage.getBoundingClientRect();
    visW = Math.max(1, Math.round(r.width));
    visH = Math.max(1, Math.round(r.height));
    leadOn = getComputedStyle(lead).display !== 'none';
    spread = visW < 700 ? 0.78 : 1;

    visOX = r.left - sr.left;
    visOY = r.top - sr.top;
    var cr = cardsBox.getBoundingClientRect();
    cardX = cr.left - sr.left;
    cardAnchorY = clamp(cr.top + Math.min(cr.height, 130) * 0.5 - sr.top, 8, sr.height - 8);

    if (three) {
      three.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, dprCapNow));
      three.renderer.setSize(visW, visH, false);
      three.camera.aspect = visW / visH;
      three.camera.updateProjectionMatrix();
    }
    dirty = true;
  }

  if ('ResizeObserver' in window) new ResizeObserver(measure).observe(vis);
  window.addEventListener('resize', measure);
  window.addEventListener('orientationchange', function () { setTimeout(measure, 250); });
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(measure);

  /* --- 6. Форма --------------------------------------------------------- */
  var form = document.getElementById('form');
  var formOut = document.getElementById('formOut');
  var mail = document.getElementById('mail');

  form.addEventListener('submit', function (e) {
    e.preventDefault();
    var v = mail.value.trim();
    if (!v || v.indexOf('@') < 1 || v.indexOf('.', v.indexOf('@')) < 0) {
      formOut.textContent = 'Схоже, у адресі помилка. Перевір її — і спробуй ще раз.';
      mail.focus();
      return;
    }
    formOut.textContent = 'Нічого не надіслано. Кресало К1 — вигаданий продукт, форма ні з чим ' +
      'не з’єднана: адреса залишилася у вкладці й зникне разом з нею.';
  });

  /* --- 7. Процедурні текстури ------------------------------------------
     Малюються кодом при старті. Жоден файл не завантажується. */
  function cv(w, h) {
    var c = document.createElement('canvas');
    c.width = w; c.height = h;
    return c;
  }

  // простий детермінований генератор, щоб малюнок був той самий щоразу
  function rng(seed) {
    return function () { seed = (seed * 1664525 + 1013904223) % 4294967296; return seed / 4294967296; };
  }

  function boardTexture(THREE) {
    var c = cv(1024, 512), x = c.getContext('2d'), rnd = rng(7);
    x.fillStyle = '#3B2A57'; x.fillRect(0, 0, 1024, 512);

    // мідні доріжки
    x.lineCap = 'round';
    for (var i = 0; i < 46; i++) {
      x.strokeStyle = 'rgba(184,115,51,' + (0.35 + rnd() * 0.5).toFixed(2) + ')';
      x.lineWidth = 1 + Math.round(rnd() * 2);
      var px = rnd() * 1024, py = rnd() * 512;
      x.beginPath(); x.moveTo(px, py);
      for (var s = 0; s < 4; s++) {
        px += (rnd() - 0.5) * 260;
        py += (rnd() < 0.5 ? -1 : 1) * rnd() * 90;
        x.lineTo(Math.round(px), Math.round(py));
      }
      x.stroke();
    }

    // перехідні отвори
    for (var v = 0; v < 90; v++) {
      x.fillStyle = '#C98A4B';
      x.beginPath(); x.arc(rnd() * 1024, rnd() * 512, 2.6, 0, 6.283); x.fill();
    }

    // шовкографія
    x.fillStyle = 'rgba(231,228,220,0.82)';
    x.font = '500 15px ui-monospace, monospace';
    var marks = ['К1-03', 'U1', 'U2', 'U3', 'J1', 'GPIO 1—40', 'REV.C', 'C11', 'R7'];
    for (var m = 0; m < marks.length; m++) {
      x.fillText(marks[m], 40 + (m % 3) * 330, 60 + Math.floor(m / 3) * 150);
    }
    x.strokeStyle = 'rgba(231,228,220,0.5)'; x.lineWidth = 2;
    x.strokeRect(26, 26, 1024 - 52, 512 - 52);

    var t = new THREE.CanvasTexture(c);
    t.colorSpace = THREE.SRGBColorSpace;
    t.anisotropy = 4;
    return t;
  }

  function labelTexture(THREE) {
    var c = cv(512, 180), x = c.getContext('2d');
    x.fillStyle = '#E7E4DC'; x.fillRect(0, 0, 512, 180);
    x.fillStyle = '#1A1C20';
    x.font = '600 34px ui-monospace, monospace';
    x.fillText('6000 мА·год', 26, 64);
    x.font = '400 24px ui-monospace, monospace';
    x.fillText('Li-ion · 3,85 В · знімний', 26, 104);
    x.fillRect(26, 126, 300, 3);
    x.font = '400 20px ui-monospace, monospace';
    x.fillText('К1-04 · заміна без інструменту', 26, 158);
    var t = new THREE.CanvasTexture(c);
    t.colorSpace = THREE.SRGBColorSpace;
    return t;
  }

  // Екран живий, але без вмісту: рівне матове підсвічування й слабкий
  // відблиск антиблікового покриття. Жодних термінальних логів.
  function screenTexture(THREE) {
    var c = cv(256, 128), x = c.getContext('2d');
    var g = x.createRadialGradient(128, 58, 10, 128, 64, 150);
    g.addColorStop(0, '#3A4E5A');
    g.addColorStop(0.55, '#22323C');
    g.addColorStop(1, '#131C22');
    x.fillStyle = g; x.fillRect(0, 0, 256, 128);
    var sheen = x.createLinearGradient(0, 0, 256, 128);
    sheen.addColorStop(0, 'rgba(255,255,255,0.05)');
    sheen.addColorStop(0.45, 'rgba(255,255,255,0)');
    x.fillStyle = sheen; x.fillRect(0, 0, 256, 128);
    var t = new THREE.CanvasTexture(c);
    t.colorSpace = THREE.SRGBColorSpace;
    return t;
  }

  // шліфування алюмінію — тонкі штрихи в шорсткості
  function brushTexture(THREE) {
    var c = cv(256, 256), x = c.getContext('2d'), rnd = rng(3);
    x.fillStyle = '#8a8a8a'; x.fillRect(0, 0, 256, 256);
    for (var i = 0; i < 900; i++) {
      var a = 0.04 + rnd() * 0.08;
      x.strokeStyle = (rnd() < 0.5 ? 'rgba(255,255,255,' : 'rgba(0,0,0,') + a.toFixed(2) + ')';
      x.lineWidth = rnd() * 1.6;
      var y = rnd() * 256;
      x.beginPath(); x.moveTo(rnd() * 60, y); x.lineTo(60 + rnd() * 220, y + (rnd() - 0.5) * 2); x.stroke();
    }
    var t = new THREE.CanvasTexture(c);
    t.wrapS = t.wrapT = THREE.RepeatWrapping;
    t.repeat.set(3, 2);
    return t;
  }

  // М'яка пляма — тінь однієї деталі на тій, що під нею
  function shadowTexture(THREE) {
    var c = cv(128, 128), x = c.getContext('2d');
    var g = x.createRadialGradient(64, 64, 4, 64, 64, 62);
    g.addColorStop(0, 'rgba(0,0,0,0.85)');
    g.addColorStop(0.55, 'rgba(0,0,0,0.42)');
    g.addColorStop(1, 'rgba(0,0,0,0)');
    x.fillStyle = g; x.fillRect(0, 0, 128, 128);
    return new THREE.CanvasTexture(c);
  }

  // М'яке світіння над матрицею — дешевша заміна повного bloom
  function glowTexture(THREE) {
    var c = cv(128, 128), x = c.getContext('2d');
    var g = x.createRadialGradient(64, 64, 2, 64, 64, 62);
    g.addColorStop(0, 'rgba(150,200,230,0.9)');
    g.addColorStop(0.45, 'rgba(110,165,205,0.32)');
    g.addColorStop(1, 'rgba(90,140,190,0)');
    x.fillStyle = g; x.fillRect(0, 0, 128, 128);
    return new THREE.CanvasTexture(c);
  }

  /* Оточення для відображень. Тут важлива не яскравість, а КОНТРАСТ:
     плавний градієнт дає рівне відображення, і метал читається як пластик.
     Метал упізнається за тим, що по ньому їдуть світлі смуги на темному —
     тому це темна студія з кількома різкими софтбоксами. */
  function envTexture(THREE) {
    var c = cv(512, 256), x = c.getContext('2d');

    var g = x.createLinearGradient(0, 0, 0, 256);
    g.addColorStop(0, '#8e939c');   // стеля
    g.addColorStop(0.44, '#4a4e56');
    g.addColorStop(0.54, '#26282d');
    g.addColorStop(1, '#0e0f12');   // підлога
    x.fillStyle = g; x.fillRect(0, 0, 512, 256);

    function strip(cx, cy, w, h, col) {
      var s = x.createLinearGradient(cx - w / 2, cy, cx + w / 2, cy);
      s.addColorStop(0, 'rgba(0,0,0,0)');
      s.addColorStop(0.5, col);
      s.addColorStop(1, 'rgba(0,0,0,0)');
      x.fillStyle = s;
      x.fillRect(cx - w / 2, cy - h / 2, w, h);
    }

    strip(120, 44, 250, 34, 'rgba(255,255,255,1)');      // головний софтбокс
    strip(310, 26, 190, 20, 'rgba(236,242,255,0.95)');   // холодний згори
    strip(415, 98, 200, 26, 'rgba(255,196,138,0.9)');    // теплий збоку
    strip(30,  126, 150, 14, 'rgba(196,214,240,0.6)');   // слабкий контровий

    var t = new THREE.CanvasTexture(c);
    t.mapping = THREE.EquirectangularReflectionMapping;
    t.colorSpace = THREE.SRGBColorSpace;
    return t;
  }

  /* --- 8. Сцена --------------------------------------------------------- */
  function noThree() {
    root.classList.add('no3d');
    three = null;
    measure();
    dirty = true;
    if (ann && !ann.textContent) ann.textContent = '3D-сцена недоступна. Шари показано схемою.';
  }

  function hasWebGL() {
    try {
      var c = document.createElement('canvas');
      var gl = c.getContext('webgl2') || c.getContext('webgl');
      if (!gl) return false;
      var lose = gl.getExtension('WEBGL_lose_context');
      if (lose) lose.loseContext();
      return true;
    } catch (e) { return false; }
  }

  function build(THREE, renderer) {
    var scene = new THREE.Scene();
    var camera = new THREE.PerspectiveCamera(42, 1, 0.6, 60);

    var pmrem = new THREE.PMREMGenerator(renderer);
    var envTex = envTexture(THREE);
    scene.environment = pmrem.fromEquirectangular(envTex).texture;
    envTex.dispose();
    pmrem.dispose();

    var hemi = new THREE.HemisphereLight(0xE7E4DC, 0x241C33, 0.6);
    var key  = new THREE.DirectionalLight(0xFFF6EC, 1.8); key.position.set(3.4, 6.2, 4.2);
    var rim  = new THREE.DirectionalLight(0xC9773F, 0.7);  rim.position.set(-4.2, -1.2, -3.6);
    scene.add(hemi, key, rim);

    var brush = brushTexture(THREE);

    function std(o) { return new THREE.MeshStandardMaterial(o); }

    var texBoard = boardTexture(THREE), texLabel = labelTexture(THREE), texScreen = screenTexture(THREE);

    /* Металічність навмисне не 1,0: на схемі деталь має лишатися читабельною
       навіть там, де їй нема чого відбивати. Трохи дифузного кольору — і
       алюміній не провалюється в чорноту, коли повертається до темної стіни.

       Набір створюється окремо для кожного шару: спільні матеріали не дали б
       притлумити неактивні деталі, не зачепивши активну. Текстури при цьому
       спільні — дублюється лише опис поверхні, не пікселі. */
    function makeMats() {
      return {
        alu:   std({ color: 0xAEB3AE, metalness: 0.72, roughness: 0.31, roughnessMap: brush, envMapIntensity: 1.35 }),
        aluIn: std({ color: 0x7D827E, metalness: 0.62, roughness: 0.50, roughnessMap: brush, envMapIntensity: 1.10 }),
        cu:    std({ color: 0xC0703A, metalness: 0.82, roughness: 0.26, envMapIntensity: 1.45 }),
        cuDim: std({ color: 0xA55C2C, metalness: 0.82, roughness: 0.42, envMapIntensity: 1.20 }),
        dark:  std({ color: 0x1E2024, metalness: 0.18, roughness: 0.62 }),
        keyc:  std({ color: 0x24272B, metalness: 0.10, roughness: 0.55 }),
        board: std({ color: 0xFFFFFF, metalness: 0.05, roughness: 0.55, map: texBoard }),
        label: std({ color: 0xFFFFFF, metalness: 0.00, roughness: 0.90, map: texLabel }),
        glass: std({ color: 0x0E1518, metalness: 0, roughness: 0.72,
                     emissive: 0xFFFFFF, emissiveIntensity: 0.85, emissiveMap: texScreen })
      };
    }

    var sets = [], layerMats = [], allMats = [];
    for (var si = 0; si < 6; si++) {
      var set = makeMats(), list = [];
      for (var kk in set) {
        var mm = set[kk];
        list.push({ m: mm, c: mm.color.clone(), e: mm.envMapIntensity, ei: mm.emissiveIntensity });
        allMats.push(mm);
      }
      sets.push(set);
      layerMats.push(list);
    }

    /* Коробка з фаскою по всіх ребрах. Саме фаска ловить світло вузькою
       смужкою — це те, за чим око впізнає фрезероване з металу. */
    function chamferGeo(w, h, d, c) {
      var sh = new THREE.Shape();
      var hw = w / 2 - c, hd = d / 2 - c;
      sh.moveTo(-hw, -hd); sh.lineTo(hw, -hd); sh.lineTo(hw, hd); sh.lineTo(-hw, hd); sh.closePath();
      var g = new THREE.ExtrudeGeometry(sh, {
        depth: Math.max(0.001, h - 2 * c), bevelEnabled: true,
        bevelSize: c, bevelThickness: c, bevelSegments: 1, curveSegments: 1, steps: 1
      });
      g.rotateX(-Math.PI / 2);
      g.translate(0, -h / 2 + c, 0);
      return g;
    }

    function part(w, h, d, mat, x, y, z, c) {
      var m = new THREE.Mesh(chamferGeo(w, h, d, c === undefined ? Math.min(0.012, h * 0.3) : c), mat);
      m.position.set(x || 0, y || 0, z || 0);
      return m;
    }

    function plainPart(w, h, d, mat, x, y, z) {
      var m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), mat);
      m.position.set(x || 0, y || 0, z || 0);
      return m;
    }

    var groups = [], anchors = [];
    for (var i = 0; i < 6; i++) { var g = new THREE.Group(); groups.push(g); scene.add(g); }

    var M0 = sets[0], M1 = sets[1], M2 = sets[2], M3 = sets[3], M4 = sets[4], M5 = sets[5];

    /* 01 екран */
    groups[0].add(
      part(3.86, 0.030, 1.00, M0.alu, 0, 0, -0.52),
      part(3.34, 0.014, 0.76, M0.dark, 0, 0.020, -0.52, 0.004),
      plainPart(3.20, 0.006, 0.64, M0.glass, 0, 0.030, -0.52)
    );

    /* 02 клавіатура */
    groups[1].add(part(3.86, 0.028, 1.02, M1.aluIn, 0, 0, 0.52));
    var keys = new THREE.InstancedMesh(chamferGeo(0.235, 0.060, 0.150, 0.016), M1.keyc, 62);
    var dummy = new THREE.Object3D(), n = 0;
    for (var r = 0; r < 5 && n < 62; r++) {
      for (var c2 = 0; c2 < 13 && n < 62; c2++) {
        dummy.position.set(-1.72 + c2 * 0.2867, 0.044, 0.17 + r * 0.190);
        dummy.updateMatrix();
        keys.setMatrixAt(n++, dummy.matrix);
      }
    }
    keys.instanceMatrix.needsUpdate = true;
    groups[1].add(keys);

    /* 03 плата */
    groups[2].add(
      part(3.78, 0.028, 2.00, M2.board, 0, 0, 0, 0.006),
      part(0.62, 0.050, 0.62, M2.dark, -0.90, 0.039, -0.20, 0.008),
      part(0.40, 0.035, 0.75, M2.dark,  0.60, 0.032,  0.10, 0.008),
      part(0.30, 0.030, 0.30, M2.dark,  1.30, 0.029, -0.50, 0.006),
      part(0.35, 0.060, 0.16, M2.cuDim, 1.55, 0.044,  0.85, 0.008)
    );
    var pins = new THREE.InstancedMesh(new THREE.BoxGeometry(0.030, 0.075, 0.030), M2.cu, 20);
    for (var p2 = 0; p2 < 20; p2++) {
      dummy.position.set(-1.00 + p2 * 0.105, 0.050, 0.92);
      dummy.updateMatrix();
      pins.setMatrixAt(p2, dummy.matrix);
    }
    pins.instanceMatrix.needsUpdate = true;
    groups[2].add(pins);

    /* 04 акумулятор */
    groups[3].add(
      part(3.10, 0.155, 1.72, M3.dark, 0, 0, 0, 0.018),
      plainPart(1.42, 0.003, 0.50, M3.label, -0.30, 0.079, 0.10),
      part(0.12, 0.040, 0.16, M3.cu, -1.50, 0.040, -0.30, 0.008),
      part(0.12, 0.040, 0.16, M3.cu, -1.50, 0.040,  0.30, 0.008)
    );

    /* 05 радіатор */
    groups[4].add(part(3.70, 0.045, 1.95, M4.cu, 0, -0.010, 0, 0.010));
    var fins = new THREE.InstancedMesh(chamferGeo(0.045, 0.075, 1.62, 0.010), M4.cuDim, 15);
    for (var f = 0; f < 15; f++) {
      dummy.position.set(-1.61 + f * 0.23, 0.050, 0);
      dummy.updateMatrix();
      fins.setMatrixAt(f, dummy.matrix);
    }
    fins.instanceMatrix.needsUpdate = true;
    groups[4].add(fins);

    /* 06 корпус: дно, стінки, приливи під гвинти, ребра жорсткості.
       Передня стінка складена з чотирьох сегментів — прорізи між ними і є
       роз'єми, які видно, коли корпус від'їжджає вниз. */
    groups[5].add(
      part(4.00, 0.050, 2.20, M5.alu, 0, -0.205, 0, 0.014),
      part(0.06, 0.42, 2.20, M5.alu, -1.97, 0, 0, 0.012),
      part(0.06, 0.42, 2.20, M5.alu,  1.97, 0, 0, 0.012),
      part(4.00, 0.42, 0.06, M5.alu, 0, 0, -1.07, 0.012),
      part(0.88, 0.42, 0.06, M5.alu, -1.56, 0, 1.07, 0.012),
      part(0.68, 0.42, 0.06, M5.alu, -0.44, 0, 1.07, 0.012),
      part(0.77, 0.42, 0.06, M5.alu,  0.485, 0, 1.07, 0.012),
      part(0.97, 0.42, 0.06, M5.alu,  1.515, 0, 1.07, 0.012),
      // самі роз'єми
      part(0.32, 0.105, 0.09, M5.dark, -0.95, 0, 1.055, 0.012),
      part(0.20, 0.055, 0.08, M5.dark,  0.00, 0, 1.055, 0.010),
      part(0.15, 0.130, 0.08, M5.dark,  0.95, 0, 1.055, 0.020),
      part(0.24, 0.030, 0.05, M5.cuDim, -0.95, 0, 1.045, 0.006)
    );
    // ребра жорсткості на дні
    for (var rb = -1; rb <= 1; rb++) {
      groups[5].add(part(0.05, 0.075, 1.86, M5.aluIn, rb * 1.02, -0.145, 0, 0.010));
    }
    // приливи під гвинти
    var bossGeo = new THREE.CylinderGeometry(0.082, 0.095, 0.16, 10);
    var bosses = new THREE.InstancedMesh(bossGeo, M5.aluIn, 6);
    var screwPos = [[-1.85, 0.92], [-1.85, 0], [-1.85, -0.92], [1.85, 0.92], [1.85, 0], [1.85, -0.92]];
    for (var bi = 0; bi < 6; bi++) {
      dummy.position.set(screwPos[bi][0], -0.10, screwPos[bi][1]);
      dummy.updateMatrix();
      bosses.setMatrixAt(bi, dummy.matrix);
    }
    bosses.instanceMatrix.needsUpdate = true;
    groups[5].add(bosses);

    // шість гвинтів — вони ж перший такт анімації
    var scGeo = new THREE.CylinderGeometry(0.058, 0.052, 0.026, 12);
    var caseScrews = new THREE.InstancedMesh(scGeo, M5.cuDim, 6);
    groups[5].add(caseScrews);

    /* М'які тіні. Кидає не «шар на наступний», а той, що фізично над ним:
       екран і клавіатура лежать у різних половинах, тож обидва падають на плату. */
    var shTex = shadowTexture(THREE);
    var SHADOWS = [
      { from: 0, to: 2, w: 3.95, d: 1.10, x: 0, z: -0.52, y:  0.017 },
      { from: 1, to: 2, w: 3.95, d: 1.12, x: 0, z:  0.52, y:  0.017 },
      { from: 2, to: 3, w: 3.85, d: 2.05, x: 0, z:  0,    y:  0.081 },
      { from: 3, to: 4, w: 3.20, d: 1.80, x: 0, z:  0,    y:  0.092 },
      { from: 4, to: 5, w: 3.80, d: 2.02, x: 0, z:  0,    y: -0.176 }
    ];
    var shadows = [];
    for (var sd = 0; sd < SHADOWS.length; sd++) {
      var S = SHADOWS[sd];
      var sm = new THREE.MeshBasicMaterial({
        map: shTex, transparent: true, depthWrite: false, opacity: 0, toneMapped: false
      });
      var pl = new THREE.Mesh(new THREE.PlaneGeometry(1, 1), sm);
      pl.rotation.x = -Math.PI / 2;
      pl.position.set(S.x, S.y, S.z);
      pl.scale.set(S.w, S.d, 1);
      pl.renderOrder = -1;
      groups[S.to].add(pl);
      shadows.push({ mesh: pl, mat: sm, spec: S });
    }

    /* Світіння екрана. Повний ланцюг постобробки заради однієї яскравої
       ділянки коштував би ще чотирьох запитів до CDN і ламався б на
       прозорому тлі; адитивний квадрат дає той самий ефект задарма. */
    var glow = new THREE.Mesh(
      new THREE.PlaneGeometry(1, 1),
      new THREE.MeshBasicMaterial({
        map: glowTexture(THREE), transparent: true, depthWrite: false,
        blending: THREE.AdditiveBlending, opacity: 0.6, toneMapped: false
      })
    );
    glow.rotation.x = -Math.PI / 2;
    glow.position.set(0, 0.042, -0.52);
    glow.scale.set(3.9, 1.25, 1);
    glow.renderOrder = 2;
    groups[0].add(glow);

    var ap = [
      [1.86, 0.03, -0.85], [1.86, 0.03, 0.85], [1.82, 0.04, 0.85],
      [1.48, 0.09, 0.80], [1.78, 0.05, 0.90], [1.94, 0.20, 1.02]
    ];
    for (var a = 0; a < 6; a++) {
      var o = new THREE.Object3D();
      o.position.set(ap[a][0], ap[a][1], ap[a][2]);
      groups[a].add(o);
      anchors.push(o);
    }

    return {
      scene: scene, camera: camera, groups: groups, anchors: anchors,
      mats: allMats, layerMats: layerMats, shadows: shadows, glow: glow,
      hemi: hemi, key: key, rim: rim,
      caseScrews: caseScrews, screwPos: screwPos, dummy: dummy,
      vec: new THREE.Vector3()
    };
  }

  function applyThree(p, collapse, dt, idx) {
    var i, L, lo = 1e9, hi = -1e9;

    for (i = 0; i < 6; i++) {
      L = LAYERS[i];
      three.groups[i].position.set(us[i] * L.dx, ys[i], us[i] * L.dz);
      three.groups[i].rotation.set(us[i] * L.rx, 0, us[i] * L.rz);
      if (ys[i] - L.half < lo) lo = ys[i] - L.half;
      if (ys[i] + L.half > hi) hi = ys[i] + L.half;
    }

    /* Активний шар світиться на повну, решта притлумлюється. Робимо це
       кольором і силою відображень, а не прозорістю: напівпрозорі деталі
       довелося б сортувати, і вони почали б проступати одна крізь одну. */
    for (i = 0; i < 6; i++) {
      var tgt = (i === idx) ? 1 : 0.4;
      dims[i] += (tgt - dims[i]) * (1 - Math.exp(-7 * Math.max(dt, 0.001)));
      if (Math.abs(dims[i] - dimsPrev[i]) < 0.002) continue;
      dimsPrev[i] = dims[i];
      var lm = three.layerMats[i], fk = dims[i];
      for (var j = 0; j < lm.length; j++) {
        var em = lm[j];
        em.m.color.copy(em.c).multiplyScalar(0.34 + 0.66 * fk);
        em.m.envMapIntensity = em.e * (0.35 + 0.65 * fk);
        if (em.ei) em.m.emissiveIntensity = em.ei * (0.25 + 0.75 * fk);
      }
    }

    if (three.glow.visible) three.glow.material.opacity = 0.22 + 0.5 * dims[0];

    // М'яка тінь верхньої деталі на тій, що під нею: щільна, поки вони поруч,
    // і розмита та бліда, коли роз'їхалися.
    for (var sI = 0; sI < three.shadows.length; sI++) {
      var sh = three.shadows[sI], S = sh.spec;
      var gap = (ys[S.from] - LAYERS[S.from].half) - (ys[S.to] + LAYERS[S.to].half);
      var op = 0.55 * (1 - clamp(gap / 1.1, 0, 1)) * (0.35 + 0.65 * dims[S.to]);
      sh.mesh.visible = fxOn && op > 0.012;
      if (!sh.mesh.visible) continue;
      sh.mat.opacity = op;
      var kk = clamp(1 + gap * 0.22, 0.95, 1.7);
      sh.mesh.scale.set(S.w * kk, S.d * kk, 1);
      sh.mesh.position.x = S.x + (us[S.from] * LAYERS[S.from].dx - us[S.to] * LAYERS[S.to].dx);
      sh.mesh.position.z = S.z + (us[S.from] * LAYERS[S.from].dz - us[S.to] * LAYERS[S.to].dz);
    }

    // Гвинти: викручуються на самому початку і вкручуються назад у фіналі.
    var sf = win(SCREW_A, SCREW_B, p) * (1 - collapse);
    var d = three.dummy, sp = three.screwPos;
    for (i = 0; i < 6; i++) {
      var lag = clamp((sf - i * 0.06) / 0.7, 0, 1);
      var e = easeOut(lag, 2);
      d.position.set(sp[i][0], 0.20 + e * 0.40, sp[i][1]);
      d.rotation.set(0, e * 9.2, 0);
      var s = 1 - smoothstep(0.72, 1, e);
      d.scale.set(s, s, s);
      d.updateMatrix();
      three.caseScrews.setMatrixAt(i, d.matrix);
    }
    d.scale.set(1, 1, 1);
    d.rotation.set(0, 0, 0);
    three.caseScrews.instanceMatrix.needsUpdate = true;

    var cam = three.camera;
    var cy = (lo + hi) / 2;
    // Кут підйому майже сталий: разом зі зростанням відстані це дає рівно те,
    // що просив бриф — камера піднімається, відводиться, і стос видно збоку,
    // а не згори. Нижче ~24° верхні шари опиняються над камерою.
    var el = (28 - 3.5 * p) * Math.PI / 180;
    // У кадр треба вмістити не лише висоту стосу: нахилена камера проєктує
    // ще й глибину пристрою у вертикаль, інакше нижня деталь зрізається.
    var halfH = (hi - lo) / 2 + 1.15 * Math.sin(el) + 0.22;
    var tv = Math.tan(21 * Math.PI / 180);
    var aspect = Math.max(0.35, visW / visH);
    var dist = Math.max(halfH / tv, 2.46 / (tv * aspect), 3.2) * 1.10;
    var az = 0.36 + (reduced ? 0 : Math.sin(performance.now() / 4200) * (0.14 - 0.09 * p));
    var ch = Math.cos(el) * dist;
    cam.position.set(Math.sin(az) * ch, cy + Math.sin(el) * dist, Math.cos(az) * ch);
    cam.lookAt(0, cy, 0);

    // активна деталь підходить трохи до камери — саме «трохи», щоб не збити кадр
    var fx = cam.position.x, fy = cam.position.y - cy, fz = cam.position.z;
    var fl = Math.sqrt(fx * fx + fy * fy + fz * fz) || 1;
    var kf = 0.18 * clamp((dims[idx] - 0.4) / 0.6, 0, 1);
    three.groups[idx].position.x += fx / fl * kf;
    three.groups[idx].position.y += fy / fl * kf;
    three.groups[idx].position.z += fz / fl * kf;

    three.renderer.render(three.scene, cam);

    if (!leadOn) { if (lead.style.opacity !== '0') lead.style.opacity = '0'; return; }

    cam.updateMatrixWorld(true);
    three.scene.updateMatrixWorld(true);
    var v = three.vec;
    three.anchors[idx].getWorldPosition(v);
    v.project(cam);

    var onScreen = v.z <= 1 && Math.abs(v.x) < 0.98 && Math.abs(v.y) < 0.98;
    var lop = onScreen ? smoothstep(0.05, 0.35, us[idx]) * (1 - collapse) : 0;
    lead.style.opacity = lop.toFixed(2);
    if (lop <= 0) return;

    var x = visOX + (v.x * 0.5 + 0.5) * visW;
    var y2 = visOY + (-v.y * 0.5 + 0.5) * visH;
    var sx = cardX - 4, sy = cardAnchorY;
    leadLine.setAttribute('points', sx + ',' + sy + ' ' + (sx - 28) + ',' + sy + ' ' + x.toFixed(1) + ',' + y2.toFixed(1));
    leadRing.setAttribute('cx', x.toFixed(1)); leadRing.setAttribute('cy', y2.toFixed(1));
    leadDot.setAttribute('cx', x.toFixed(1));  leadDot.setAttribute('cy', y2.toFixed(1));
  }

  function initThree() {
    var THREE = window.THREE;
    if (!THREE || !hasWebGL()) { noThree(); return; }

    var renderer;
    try {
      dprCapNow = window.innerWidth < 768 ? 1.5 : 2;
      var dpr = Math.min(window.devicePixelRatio || 1, dprCapNow);
      renderer = new THREE.WebGLRenderer({
        canvas: canvas, alpha: true, antialias: dpr <= 1.5, powerPreference: 'high-performance'
      });
      renderer.setPixelRatio(dpr);
      renderer.setClearAlpha(0);
      renderer.toneMapping = THREE.ACESFilmicToneMapping;
    } catch (e) { noThree(); return; }

    var built = build(THREE, renderer);
    three = {
      renderer: renderer, scene: built.scene, camera: built.camera,
      groups: built.groups, anchors: built.anchors, mats: built.mats,
      layerMats: built.layerMats, shadows: built.shadows, glow: built.glow,
      hemi: built.hemi, key: built.key, rim: built.rim,
      caseScrews: built.caseScrews, screwPos: built.screwPos, dummy: built.dummy,
      vec: built.vec
    };

    canvas.addEventListener('webglcontextlost', function (e) {
      e.preventDefault();
      sleep();
      setTimeout(function () { if (three && !three.renderer.getContext().isContextLost) return; noThree(); }, 3000);
    });
    canvas.addEventListener('webglcontextrestored', function () { if (running) wake(); });

    onTheme();
    applyFx();
    measure();
    dirty = true;
    if (running) wake();
  }

  /* --- 9. Старт --------------------------------------------------------- */
  labelTheme();
  applyFx();
  setActive(0);
  measure();
  wake();

  if (window.THREE) initThree();
  else window.addEventListener('three:ready', initThree, { once: true });

  setTimeout(function () { if (!three && !root.classList.contains('no3d')) noThree(); }, 4000);
})();
