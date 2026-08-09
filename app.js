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
   • якщо three.js або WebGL недоступні — та сама змінна прогресу керує
     плоскою схемою, і сторінка лишається робочою.
   ========================================================================= */
(function () {
  'use strict';

  /* --- дані шарів ------------------------------------------------------- */
  // seat — де шар сидить у зібраному пристрої (світові одиниці, 1 ≈ 37 мм)
  // travel — куди він доїжджає; ease — показник кривої; dx/dz — бічний знос
  var LAYERS = [
    { no: '01', name: 'екран',      seat:  0.222, half: 0.035, travel:  3.30, ease: 3, dx:  0.10, dz: -0.04, rz:  0.020, rx: 0 },
    { no: '02', name: 'клавіатура', seat:  0.225, half: 0.040, travel:  2.00, ease: 4, dx: -0.08, dz:  0.05, rz: -0.015, rx: 0 },
    { no: '03', name: 'плата',      seat:  0.150, half: 0.045, travel:  0.85, ease: 3, dx:  0.05, dz:  0.06, rz: 0,      rx:  0.012 },
    { no: '04', name: 'акумулятор', seat:  0.030, half: 0.085, travel: -0.45, ease: 2, dx:  0.07, dz: -0.03, rz: 0,      rx: -0.010 },
    { no: '05', name: 'радіатор',   seat: -0.130, half: 0.075, travel: -1.70, ease: 3, dx: -0.05, dz:  0.04, rz:  0.014, rx: 0 },
    { no: '06', name: 'корпус',     seat: -0.030, half: 0.245, travel: -3.00, ease: 4, dx:  0,    dz:  0,    rz: 0,      rx:  0.008 }
  ];

  var LEAD = 0.03;     // мертвий хід на початку доріжки
  var DUR  = 0.19;     // скільки прогресу займає роз'їзд одного шару
  var STRIDE = 0.132;  // зсув між шарами; останній завершується на 0,880,
                       // решта доріжки — витримка, де стос стоїть зібрано-розібраним
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
  var ann    = document.getElementById('ann');
  var root   = document.documentElement;

  /* --- стан ------------------------------------------------------------- */
  var motionMQ = window.matchMedia('(prefers-reduced-motion: reduce)');
  var reduced = motionMQ.matches;
  var progress = 0, smoothed = 0, primed = false;
  var lastIndex = -1, lastFrame = 0, rafId = 0, running = false, dirty = true;
  var us = [0, 0, 0, 0, 0, 0];
  var three = null;          // { renderer, scene, camera, groups, anchors, vec }
  var visW = 0, visH = 0, visOX = 0, visOY = 0, cardX = 0, cardAnchorY = 0, leadOn = false, spread = 1;
  var annTimer = 0, lastDrawn = -1, staticMode = false;
  var stickyPx = 0, denom = 0;   // кешуються в measure(), не читаються щокадру

  function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }
  function easeOut(u, k) { return 1 - Math.pow(1 - u, k); }
  function smoothstep(a, b, x) { var t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); }

  /* --- 1. Гвинти-індикатори -------------------------------------------- */
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
    var target = LEAD + i * STRIDE + DUR * 0.72;              // шар уже приїхав
    var top = window.scrollY + track.getBoundingClientRect().top - stickyPx + target * denom;
    // стрибок робимо миттєвим завжди: плавний скрол на кілька тисяч пікселів
    // гірший за миттєвий для всіх, а не лише за prefers-reduced-motion
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

  /* --- 2. Прогрес і застосування --------------------------------------- */
  function layerU(i, p) {
    return easeOut(clamp((p - (LEAD + i * STRIDE)) / DUR, 0, 1), LAYERS[i].ease);
  }

  // Картка перемикається трохи згодом за початком руху шару, щоб деталь
  // на екрані вже виїжджала, коли з’являється її підпис.
  function activeFrom(p) {
    var idx = 0;
    for (var i = 0; i < LAYERS.length; i++) if (p >= LEAD + i * STRIDE + 0.045) idx = i;
    return idx;
  }

  function apply(p) {
    var i;
    for (i = 0; i < LAYERS.length; i++) us[i] = layerU(i, p);

    if (three) applyThree(p);
    else for (i = 0; i < flats.length; i++) {
      // плоска схема: та сама послідовність, у пікселях
      flats[i].style.setProperty('--y', (us[i] * LAYERS[i].travel * -22).toFixed(1));
    }

    for (i = 0; i < screws.length; i++) screws[i].style.setProperty('--u', us[i].toFixed(3));

    var idx = activeFrom(p);
    if (idx !== lastIndex) setActive(idx);
  }

  function setActive(idx) {
    lastIndex = idx;
    for (var i = 0; i < cards.length; i++) {
      // На дуже низьких екранах липкої сцени немає і всі шість карток видимі
      // списком — тоді жодна з них не має бути inert.
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

  /* --- 3. Цикл ---------------------------------------------------------- */
  function frame(now) {
    rafId = requestAnimationFrame(frame);

    var dt = Math.min((now - lastFrame) / 1000, 0.05);
    lastFrame = now;

    var t = denom > 0
      ? clamp((stickyPx - track.getBoundingClientRect().top) / denom, 0, 1)
      : 0;
    progress = t;

    if (!primed || reduced || Math.abs(t - smoothed) > 0.25) {
      smoothed = t;
      primed = true;
    } else {
      smoothed += (t - smoothed) * (1 - Math.exp(-SMOOTH_K * dt));
    }

    // під prefers-reduced-motion немає ні згладжування, ні коливання камери,
    // тож кадр перемальовується лише коли прогрес реально змінився
    if (reduced && !dirty && Math.abs(smoothed - lastDrawn) < 0.0002) return;
    lastDrawn = smoothed;
    dirty = false;

    apply(smoothed);
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

  // Обробник скролу нічого не рендерить: він лише позначає кадр брудним,
  // щоб цикл прокинувся, коли згладжування вимкнене.
  window.addEventListener('scroll', function () { dirty = true; }, { passive: true });

  motionMQ.addEventListener('change', function (e) {
    reduced = e.matches;
    primed = false;
    dirty = true;
  });

  /* --- 4. Розміри ------------------------------------------------------- */
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

    // виноска малюється у координатах .stage, щоб дотягуватися до картки
    visOX = r.left - sr.left;
    visOY = r.top - sr.top;
    var cr = cardsBox.getBoundingClientRect();
    cardX = cr.left - sr.left;
    cardAnchorY = clamp(cr.top + Math.min(cr.height, 130) * 0.5 - sr.top, 8, sr.height - 8);

    if (three) {
      var dprCap = window.innerWidth < 768 ? 1.5 : 2;
      three.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, dprCap));
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

  /* --- 5. Форма --------------------------------------------------------- */
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

  /* --- 6. Тривимірна сцена ---------------------------------------------- */
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
      if (lose) lose.loseContext();   // не займаємо один із небагатьох контекстів
      return true;
    } catch (e) { return false; }
  }

  function build(THREE) {
    var scene = new THREE.Scene();
    var camera = new THREE.PerspectiveCamera(42, 1, 0.6, 60);

    scene.add(new THREE.HemisphereLight(0xE7E4DC, 0x241C33, 1.05));
    var key = new THREE.DirectionalLight(0xFFF4EA, 1.5); key.position.set(3.4, 6.2, 4.2);
    var rim = new THREE.DirectionalLight(0xC9773F, 0.55);  rim.position.set(-4.2, -1.4, -3.4);
    scene.add(key, rim);

    var off = { polygonOffset: true, polygonOffsetFactor: 1, polygonOffsetUnits: 1 };
    function lam(c) { var m = new THREE.MeshLambertMaterial({ color: c }); Object.assign(m, off); return m; }
    var matAlu   = lam(0xC3C6C0);
    var matAluIn = lam(0x8E938F);
    var matBoard = lam(0x3E2A5C);
    var matDark  = lam(0x22242A);
    var matSilk  = lam(0xE7E4DC);
    var matBezel = lam(0x14171B);
    var matGlass = new THREE.MeshBasicMaterial({ color: 0x1B3440 });
    var matCu    = new THREE.MeshPhongMaterial({ color: 0xB87333, shininess: 22, specular: 0x5A3418 });
    Object.assign(matCu, off);
    var matEdge  = new THREE.LineBasicMaterial({ color: 0xE7E4DC, transparent: true, opacity: 0.32 });

    function box(w, h, d, mat, x, y, z) {
      var m = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), mat);
      m.position.set(x || 0, y || 0, z || 0);
      return m;
    }
    function outline(mesh) {
      return new THREE.LineSegments(new THREE.EdgesGeometry(mesh.geometry), matEdge)
        .translateX(mesh.position.x).translateY(mesh.position.y).translateZ(mesh.position.z);
    }

    var groups = [], anchors = [];
    for (var i = 0; i < 6; i++) { var g = new THREE.Group(); groups.push(g); scene.add(g); }

    /* 01 екран: рамка + скло, займає верхню половину лицевої панелі */
    var frame = box(3.86, 0.030, 1.00, matAlu, 0, 0, -0.52);
    groups[0].add(
      frame, outline(frame),
      box(3.34, 0.014, 0.76, matBezel, 0, 0.020, -0.52),
      box(3.22, 0.008, 0.66, matGlass, 0, 0.028, -0.52)
    );

    /* 02 клавіатура: плита + 62 клавіші */
    var kplate = box(3.86, 0.028, 1.02, matAluIn, 0, 0, 0.52);
    groups[1].add(kplate, outline(kplate));
    var keyGeo = new THREE.BoxGeometry(0.235, 0.060, 0.150);
    var keys = new THREE.InstancedMesh(keyGeo, matDark, 62);
    var dummy = new THREE.Object3D(), n = 0;
    for (var r = 0; r < 5 && n < 62; r++) {
      for (var c = 0; c < 13 && n < 62; c++) {
        dummy.position.set(-1.72 + c * 0.2867, 0.044, 0.17 + r * 0.190);
        dummy.updateMatrix();
        keys.setMatrixAt(n++, dummy.matrix);
      }
    }
    keys.instanceMatrix.needsUpdate = true;
    groups[1].add(keys);

    /* 03 плата: текстоліт, мікросхеми, гребінка GPIO */
    var board = box(3.78, 0.028, 2.00, matBoard);
    groups[2].add(
      board, outline(board),
      box(0.62, 0.050, 0.62, matDark, -0.90, 0.039, -0.20),
      box(0.40, 0.035, 0.75, matDark,  0.60, 0.032,  0.10),
      box(0.30, 0.030, 0.30, matDark,  1.30, 0.029, -0.50),
      box(0.35, 0.060, 0.16, matCu,    1.55, 0.044,  0.85)
    );
    var pinGeo = new THREE.BoxGeometry(0.030, 0.075, 0.030);
    var pins = new THREE.InstancedMesh(pinGeo, matCu, 20);
    for (var p = 0; p < 20; p++) {
      dummy.position.set(-1.00 + p * 0.105, 0.050, 0.92);
      dummy.updateMatrix();
      pins.setMatrixAt(p, dummy.matrix);
    }
    pins.instanceMatrix.needsUpdate = true;
    groups[2].add(pins);

    /* 04 акумулятор */
    var batt = box(3.10, 0.155, 1.72, matDark);
    groups[3].add(
      batt, outline(batt),
      box(1.50, 0.004, 0.50, matSilk, -0.30, 0.080, 0.10),
      box(0.12, 0.040, 0.16, matCu, -1.50, 0.040, -0.30),
      box(0.12, 0.040, 0.16, matCu, -1.50, 0.040,  0.30)
    );

    /* 05 радіатор: мідна пластина + ребра */
    var plate = box(3.70, 0.045, 1.95, matCu, 0, 0.020, 0);
    groups[4].add(plate, outline(plate));
    var finGeo = new THREE.BoxGeometry(0.035, 0.090, 1.60);
    var fins = new THREE.InstancedMesh(finGeo, matCu, 11);
    for (var f = 0; f < 11; f++) {
      dummy.position.set(-1.60 + f * 0.32, -0.045, 0);
      dummy.updateMatrix();
      fins.setMatrixAt(f, dummy.matrix);
    }
    fins.instanceMatrix.needsUpdate = true;
    groups[4].add(fins);

    /* 06 корпус: дно, чотири стінки, шість гвинтів */
    var base = box(4.00, 0.050, 2.20, matAlu, 0, -0.205, 0);
    groups[5].add(
      base, outline(base),
      box(0.06, 0.42, 2.20, matAlu, -1.97, 0, 0),
      box(0.06, 0.42, 2.20, matAlu,  1.97, 0, 0),
      box(4.00, 0.42, 0.06, matAlu, 0, 0,  1.07),
      box(4.00, 0.42, 0.06, matAlu, 0, 0, -1.07)
    );
    var scGeo = new THREE.CylinderGeometry(0.055, 0.055, 0.022, 10);
    var sc = new THREE.InstancedMesh(scGeo, matCu, 6);
    var sp = [[-1.85, 0.92], [-1.85, 0], [-1.85, -0.92], [1.85, 0.92], [1.85, 0], [1.85, -0.92]];
    for (var s = 0; s < 6; s++) {
      dummy.position.set(sp[s][0], 0.20, sp[s][1]);
      dummy.updateMatrix();
      sc.setMatrixAt(s, dummy.matrix);
    }
    sc.instanceMatrix.needsUpdate = true;
    groups[5].add(sc);

    /* точки, у які влучає виноска — по одній на шар, на ближньому правому краї */
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

    return { scene: scene, camera: camera, groups: groups, anchors: anchors, vec: new THREE.Vector3() };
  }

  function applyThree(p) {
    var i, L, u, y, lo = 1e9, hi = -1e9;
    for (i = 0; i < 6; i++) {
      L = LAYERS[i]; u = us[i];
      y = L.seat + u * L.travel * spread;
      three.groups[i].position.set(u * L.dx, y, u * L.dz);
      three.groups[i].rotation.set(u * L.rx, 0, u * L.rz);
      if (y - L.half < lo) lo = y - L.half;
      if (y + L.half > hi) hi = y + L.half;
    }

    // Кадр рахується щоразу під реальний розмір стосу, а не за наперед
    // підібраними числами: тоді ніщо не вилазить ні на 16:9, ні на 360px,
    // ні при масштабі 200 %.
    var cam = three.camera;
    var cy = (lo + hi) / 2;
    var halfH = (hi - lo) / 2 + 0.30;
    var tv = Math.tan(21 * Math.PI / 180);
    var aspect = Math.max(0.35, visW / visH);
    var dist = Math.max(halfH / tv, 2.42 / (tv * aspect), 3.2) * 1.12;
    // Кут підйому майже сталий: разом зі зростанням відстані це дає рівно те,
    // що просив бриф — камера піднімається, відводиться, і стос видно збоку,
    // а не згори. Опускати кут нижче ~24° не можна: тоді верхні шари
    // опиняються над камерою і читаються як смужки.
    var el = (28 - 3.5 * p) * Math.PI / 180;
    var az = 0.36 + (reduced ? 0 : Math.sin(performance.now() / 4200) * (0.14 - 0.09 * p));
    var ch = Math.cos(el) * dist;
    cam.position.set(Math.sin(az) * ch, cy + Math.sin(el) * dist, Math.cos(az) * ch);
    cam.lookAt(0, cy, 0);

    three.renderer.render(three.scene, cam);

    if (!leadOn) { if (lead.style.opacity !== '0') lead.style.opacity = '0'; return; }

    cam.updateMatrixWorld(true);
    three.scene.updateMatrixWorld(true);
    var v = three.vec;
    three.anchors[lastIndex < 0 ? 0 : lastIndex].getWorldPosition(v);
    v.project(cam);

    var onScreen = v.z <= 1 && Math.abs(v.x) < 0.98 && Math.abs(v.y) < 0.98;
    var op = onScreen ? smoothstep(0.05, 0.35, us[lastIndex < 0 ? 0 : lastIndex]) : 0;
    lead.style.opacity = op.toFixed(2);
    if (op <= 0) return;

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
      var dprCap = window.innerWidth < 768 ? 1.5 : 2;
      var dpr = Math.min(window.devicePixelRatio || 1, dprCap);
      renderer = new THREE.WebGLRenderer({
        canvas: canvas, alpha: true, antialias: dpr <= 1.5, powerPreference: 'high-performance'
      });
      renderer.setPixelRatio(dpr);
      renderer.setClearAlpha(0);
    } catch (e) { noThree(); return; }

    var built = build(THREE);
    three = {
      renderer: renderer, scene: built.scene, camera: built.camera,
      groups: built.groups, anchors: built.anchors, vec: built.vec
    };

    canvas.addEventListener('webglcontextlost', function (e) {
      e.preventDefault();
      sleep();
      setTimeout(function () { if (three && !three.renderer.getContext().isContextLost) return; noThree(); }, 3000);
    });
    canvas.addEventListener('webglcontextrestored', function () { if (running) wake(); });

    measure();
    dirty = true;
    if (running) wake();
  }

  /* --- 7. Старт --------------------------------------------------------- */
  setActive(0);
  measure();
  wake();

  if (window.THREE) initThree();
  else window.addEventListener('three:ready', initThree, { once: true });

  // Якщо модуль не виконався взагалі (старий браузер, заблокований CDN,
  // відкрито без інтернету) — через 4 секунди вмикаємо плоску схему.
  setTimeout(function () { if (!three && !root.classList.contains('no3d')) noThree(); }, 4000);
})();
