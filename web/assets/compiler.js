(function () {
  'use strict';

  var NARROW = 600;                    /* below this width, column included */
  var R = 12;                          /* corner radius of a language box */
  var TIP = 3.3;                       /* how far an arrowhead reaches past its path */
  var STROKE = 1.6, STROKE_HOT = 2.3;  /* an arrow at rest, and under the pointer */

  var STATUSES = ['done', 'stub', 'next', 'merge', 'plan', 'hyp'];
  var DASH = { plan: '4 3', hyp: '2 3' };
  var WORD = { done: 'proved', stub: 'stub', next: 'in progress', merge: 'semantics',
               plan: 'planned', hyp: 'hypothetical' };

  var ORDER = ['proved', 'in progress', 'planned', 'stub', 'semantics', 'hypothetical'];

  function each(list, f) { Array.prototype.forEach.call(list, f); }

  function kids(el, cls) {
    return Array.prototype.filter.call(el.children, function (c) { return c.classList.contains(cls); });
  }

  function status(el) {
    for (var i = 0; i < STATUSES.length; i++) if (el.classList.contains(STATUSES[i])) return STATUSES[i];
    return 'done';
  }

  /* rendered: not hidden by a block's audience or a tab, and not inside a folded details.
     The fold is checked by hand: a browser may keep boxes for a closed details' content */
  function shown(el) {
    for (var e = el.parentElement; e; e = e.parentElement) {
      if (e.tagName === 'DETAILS' && !e.open) return false;
    }
    return el.getClientRects().length > 0;
  }

  /* hidden by a block or a tab between el and top, whether or not a fold hides it too */
  function dropped(el, top) {
    for (var e = el; e && e !== top; e = e.parentElement) {
      if (e.hidden || e.classList.contains('off')) return true;
    }
    return false;
  }

  /* choices: a details.choice folds like a stage. Open, its summary carries a row of tabs;
     a div.choice that is the first thing in the selected option continues that row after a
     separator. Folded, it is one row, and the language before it forks into a small box
     per way the sequence may end (fork, layout) */

  /* hidden by a block's audience between el and top; a tab does not count */
  function unheard(el, top) {
    for (var e = el; e && e !== top; e = e.parentElement) if (e.hidden) return true;
    return false;
  }

  function options(choice) { return kids(choice, 'option').filter(function (o) { return !o.hidden; }); }

  function select(choice) {
    var list = options(choice), want = choice.getAttribute('data-sel'), sel = null;
    list.forEach(function (o) { if (o.getAttribute('label') === want) sel = o; });
    sel = sel || list[0] || null;
    kids(choice, 'option').forEach(function (o) { o.classList.toggle('off', o !== sel); });
    return { list: list, sel: sel };
  }

  function nested(option) {
    var first = option && option.firstElementChild;
    return first && first.classList.contains('choice') ? first : null;
  }

  function tabs(root) {
    root.classList.add('tabbed');
    each(root.querySelectorAll('details.choice'), function (choice) {
      var summary = choice.querySelector(':scope > summary');
      var bar = kids(summary, 'tabs')[0];
      if (!bar) {
        bar = document.createElement('div');
        bar.className = 'tabs pills';
        var title = kids(summary, 'title')[0];
        summary.insertBefore(bar, title ? title.nextSibling : summary.firstChild);
      }
      bar.textContent = '';
      var c = choice, count = 0, first = true;
      while (c) {
        var s = select(c);
        count += s.list.length;
        if (!first) { var sep = document.createElement('span'); sep.className = 'sep'; bar.appendChild(sep); }
        first = false;
        s.list.forEach(function (o) {
          var b = document.createElement('button');
          b.type = 'button';
          b.textContent = o.getAttribute('label');
          b.setAttribute('aria-pressed', o === s.sel ? 'true' : 'false');
          b.addEventListener('click', (function (cc, name) {
            /* a button in a summary would also fold the choice */
            return function (e) { e.preventDefault(); cc.setAttribute('data-sel', name); schedule(); };
          })(c, o.getAttribute('label')));
          bar.appendChild(b);
        });
        c = nested(s.sel);
      }
      /* nothing to choose between: the options read inline, with no band and no fold */
      var single = count <= 1;
      choice.classList.toggle('single', single);
      if (single && !choice.open) choice.open = true;
      fork(choice);
    });
  }

  /* the ways a choice may end: its options with no options inside, that the reader gets */
  function leaves(choice) {
    return Array.prototype.filter.call(choice.querySelectorAll('.option'), function (o) {
      return !o.querySelector('.option') && !unheard(o, choice);
    });
  }

  /* the passes on the way to a leaf: those in the options that hold it */
  function path(choice, leaf) {
    return Array.prototype.filter.call(choice.querySelectorAll('details.pass:not(.note)'), function (p) {
      if (unheard(p, choice)) return false;
      for (var e = p.parentElement; e && e !== choice; e = e.parentElement) {
        if (e.classList.contains('option') && !e.contains(leaf)) return false;
      }
      return true;
    });
  }

  /* a box per leaf, named by its label, after the choice; shown while the choice is folded */
  function fork(choice) {
    var f = choice.nextElementSibling;
    if (!f || !f.classList.contains('fork')) {
      f = document.createElement('div');
      f.className = 'fork';
      f.setAttribute('aria-hidden', 'true');
      choice.parentNode.insertBefore(f, choice.nextSibling);
    }
    f.textContent = '';
    leaves(choice).forEach(function (leaf) {
      var langs = leaf.querySelectorAll('.lang'), last = langs[langs.length - 1];
      var b = document.createElement('div');
      b.className = 'mini ' + (last ? status(last) : 'done');
      b.textContent = leaf.getAttribute('label');
      b.setAttribute('data-status', count(path(choice, leaf)).group);
      f.appendChild(b);
    });
  }

  /* what a group of passes amounts to: the chip of a folded stage or choice, and the status
     its arrow takes */

  function count(passes) {
    var n = {}, st = passes.map(status);
    st.forEach(function (s) { n[WORD[s]] = (n[WORD[s]] || 0) + 1; });
    var words = Object.keys(n).sort(function (a, b) { return ORDER.indexOf(a) - ORDER.indexOf(b); });
    var head = passes.length + (passes.length === 1 ? ' pass' : ' passes');
    var text = !passes.length ? '' : words.length === 1 ? head + ', all ' + words[0]
      : [head].concat(words.map(function (w) { return n[w] + ' ' + w; })).join(' \u00b7 ');
    var all = function (f) { return st.length > 0 && st.every(f); };
    var group = all(function (s) { return s === 'hyp'; }) ? 'hyp'
      : st.indexOf('next') >= 0 ? 'next'
      : all(function (s) { return s === 'plan' || s === 'hyp'; }) ? 'plan' : 'done';
    return { text: text, group: group };
  }

  function stages(root) {
    each(root.querySelectorAll('details.stage, details.choice'), function (group) {
      /* a stage counts what it shows; a choice counts every option, folded or not */
      var passes = Array.prototype.filter.call(group.querySelectorAll('details.pass:not(.note)'),
        function (p) { return group.classList.contains('choice') ? !unheard(p, group) : !dropped(p, group); });
      var c = count(passes), chip = group.querySelector(':scope > summary .chip');
      group.setAttribute('data-status', c.group);
      if (chip) {
        chip.textContent = c.text;
        STATUSES.forEach(function (s) { chip.classList.remove(s); });
        chip.classList.add(c.group);
      }
    });
  }

  /* arrows: an arrowhead per status, and a harpoon, the head of a partial map, for a pass
     that may reject the program; the harpoon comes at both widths, so its barb keeps the
     width of the line */

  function harpoon(t) {
    var L = 11, c = 7, top = c - t / 2, bot = c + t / 2;
    var ux = -9.35, uy = 6.0, ul = Math.hypot(ux, uy);
    var u = [ux / ul, uy / ul], n = [-u[1], u[0]];
    var T = [L, top], B = [L + ux, top + uy];
    var B2 = [B[0] + t * n[0], B[1] + t * n[1]];
    var I0 = [T[0] + t * n[0], T[1] + t * n[1]];
    var k = (bot - I0[1]) / u[1], P = [I0[0] + k * u[0], bot];
    var f = function (v) { return +v.toFixed(3); }, pt = function (p) { return f(p[0]) + ' ' + f(p[1]); };
    return { d: 'M -2 ' + f(top) + ' L ' + pt(T) + ' L ' + pt(B) + ' L ' + pt(B2) + ' L ' + pt(P) +
                ' L -2 ' + f(bot) + ' z', px: P[0] };
  }
  var HP_REF = Math.min(harpoon(STROKE).px, harpoon(STROKE_HOT).px) - 0.3, HP_TIP = 11 - HP_REF;

  /* what may fail in a pass, or in the shown passes of a folded stage or choice, as one
     phrase: "the lexer, the parser or type inference may fail" */
  function fails(e, stage) {
    var parts = [];
    var add = function (x) {
      (x.getAttribute('data-fails') || '').split(';').forEach(function (f) {
        f = f.trim();
        if (f && parts.indexOf(f) < 0) parts.push(f);
      });
    };
    if (stage) {
      each(e.querySelectorAll('.pass.partial'), function (x) { if (!dropped(x, e)) add(x); });
    } else add(e);
    if (!parts.length) return null;
    var last = parts.pop();
    return (parts.length ? parts.join(', ') + ' or ' + last : last) + ' may fail';
  }

  function el(name, attrs) {
    var e = document.createElementNS('http://www.w3.org/2000/svg', name);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    return e;
  }

  function defs(svg, color) {
    var d = el('defs', {});
    STATUSES.forEach(function (s) {
      var m = el('marker', { id: 'cd-ah-' + s, viewBox: '0 0 10 10', refX: 7, refY: 5, markerWidth: 11,
        markerHeight: 11, markerUnits: 'userSpaceOnUse', orient: 'auto-start-reverse' });
      m.appendChild(el('path', { d: 'M 0 0 L 10 5 L 0 10 z', fill: color[s] }));
      d.appendChild(m);
      [['', STROKE], ['-h', STROKE_HOT]].forEach(function (v) {
        var h = el('marker', { id: 'cd-hp-' + s + v[0], viewBox: '-2 0 13 16', refX: +HP_REF.toFixed(3),
          refY: 7, markerWidth: 13, markerHeight: 16, markerUnits: 'userSpaceOnUse', orient: 'auto-start-reverse' });
        h.appendChild(el('path', { d: harpoon(v[1]).d, fill: color[s] }));
        d.appendChild(h);
      });
    });
    svg.appendChild(d);
  }

  /* layout: walk the rendered languages, passes, folded stages and lines in page order.
     A language box starts where the pass into it left off, or where it stands; it ends
     just above the middle of the pass that leaves it. A box too short for its text pushes
     that pass down. */

  function layout(root) {
    var svg = kids(root, 'arrows')[0];
    if (!svg) {
      svg = el('svg', { 'class': 'arrows', 'aria-hidden': 'true' });
      root.insertBefore(svg, root.firstChild);
    }
    while (svg.firstChild) svg.removeChild(svg.firstChild);
    each(root.querySelectorAll('.lang'), function (b) { b.style.top = ''; b.style.height = ''; });
    each(root.querySelectorAll('[data-pushed]'), function (e) { e.style.marginTop = ''; e.removeAttribute('data-pushed'); });
    each(root.querySelectorAll('.fork'), function (f) { f.style.height = ''; });
    root.style.minHeight = '';

    /* the language column hangs into the margin when the page leaves room for it there,
       so the passes line up with the text; otherwise it takes its width from the passes */
    root.classList.remove('laid', 'hang');
    var css = getComputedStyle(root), color = {};
    var gutter = parseFloat(css.getPropertyValue('--gutter')) || 200;
    var hang = root.getBoundingClientRect().left - gutter >= 8;
    var rows_w = root.clientWidth - (hang ? 0 : gutter);
    if (rows_w < NARROW - gutter) return;
    root.classList.add('laid');
    root.classList.toggle('hang', hang);

    STATUSES.forEach(function (s) { color[s] = css.getPropertyValue('--arrow-' + s).trim() || '#000'; });
    var noteFill = css.getPropertyValue('--merge-bg').trim() || '#ffe0c2';
    var right = parseFloat(css.getPropertyValue('--box-w')) || 150;
    defs(svg, color);

    var base = root.getBoundingClientRect().top;
    var top = function (e) { return e.getBoundingClientRect().top - base; };
    var bottom = function (e) { return e.getBoundingClientRect().bottom - base; };
    var head = function (e) { return e.querySelector(':scope > summary') || e; };
    var mid = function (e) { var r = head(e).getBoundingClientRect(); return (r.top + r.bottom) / 2 - base; };
    function push(e, dy) {
      if (dy <= 0) return;
      /* on top of the stylesheet's margin, which an inline one would otherwise replace; a
         margin that collapses with the one above moves e by less, so add what is missing */
      var t0 = top(e), m = (parseFloat(getComputedStyle(e).marginTop) || 0) + dy;
      for (var i = 0; i < 4; i++) {
        e.style.marginTop = m + 'px';
        var short = t0 + dy - top(e);
        if (short < 0.5) break;
        m += short;
      }
      e.setAttribute('data-pushed', '');
    }

    var seq = Array.prototype.filter.call(
      root.querySelectorAll('.lang, details.pass, details.stage, details.choice, .divider'), shown);
    var boxes = [], rows = [], waiting = [], cur = null, pending = null;

    seq.forEach(function (e) {
      if (e.classList.contains('lang')) {
        var t = pending != null ? pending : top(e);
        pending = null;
        if (cur) { cur.bot = Math.max(cur.last, cur.top + cur.need); boxes.push(cur); }
        cur = { el: e, top: t, need: e.offsetHeight, last: t + e.offsetHeight, status: status(e),
                floor: waiting.length ? t + 18 : null };
        waiting.forEach(function (r) { r.to = cur; });
        waiting = [];
      } else if (e.classList.contains('divider')) {
        if (cur) {
          push(e, cur.top + cur.need + 8 - top(e));
          cur.bot = Math.max(cur.last, top(e) - 8);
          boxes.push(cur);
          cur = null;
        }
        pending = null;
      } else {
        /* a folded stage or choice is one row, standing for the passes inside it */
        var choice = e.classList.contains('choice');
        var stage = choice || e.classList.contains('stage');
        if (stage && e.open) return;
        /* the first arrow out of a box starts below the arrow that comes into it */
        if (cur && cur.floor != null) { push(e, cur.floor - (mid(e) - 9)); cur.floor = null; }
        var visible = function (sel) {
          return Array.prototype.some.call(e.querySelectorAll(sel), function (x) { return !dropped(x, e); });
        };
        var r = {
          el: e, from: cur, to: cur, note: e.classList.contains('note'),
          status: stage ? e.getAttribute('data-status') || 'done' : status(e),
          cross: stage ? visible('.lang, .pass.cross') : e.classList.contains('cross'),
          partial: stage ? visible('.pass.partial') : e.classList.contains('partial'),
          fails: fails(e, stage)
        };
        if (r.cross && cur) {
          push(e, cur.top + cur.need + 5 - mid(e));
          cur.bot = mid(e) - 5;
          boxes.push(cur);
          cur = null;
          pending = (e.open && !stage ? bottom(e) : mid(e)) + 5;
          r.to = null;
          if (choice) {
            /* a folded choice ends in a box per way it may end, stacked below its row */
            var f = e.nextElementSibling, minis = f ? kids(f, 'mini') : [];
            var h = minis.length ? minis[0].offsetHeight : 0;
            if (f) f.style.height = minis.length * (h + 6) + 'px';
            r.fork = minis.map(function (b, i) {
              var t = top(f) + i * (h + 6);
              b.style.top = t + 'px';
              return { top: t, bot: t + h, status: b.getAttribute('data-status') || 'done' };
            });
            pending = null;
          } else {
            waiting.push(r);
          }
        } else if (cur) {
          cur.last = Math.max(cur.last, bottom(e));
        }
        rows.push(r);
      }
    });
    if (cur) { cur.bot = Math.max(cur.last, cur.top + cur.need); boxes.push(cur); }

    var height = root.offsetHeight;
    rows.forEach(function (r) { (r.fork || []).forEach(function (b) { height = Math.max(height, b.bot); }); });
    boxes.forEach(function (b) {
      b.el.style.top = b.top + 'px';
      b.el.style.height = (b.bot - b.top) + 'px';
      height = Math.max(height, b.bot);
    });
    if (height > root.offsetHeight) root.style.minHeight = height + 'px';
    svg.setAttribute('width', root.clientWidth);
    svg.setAttribute('height', height);

    /* x of a box's right edge at height y, inside the rounded corners */
    function edge(b, y) {
      if (!b) return right;
      var d = Math.max(0, Math.min(y - b.top, b.bot - y));
      return d >= R ? right : right - (R - Math.sqrt(R * R - (R - d) * (R - d)));
    }
    var r1 = function (v) { return Math.round(v * 10) / 10; };

    function arrow(from, y0, to, y1, s, partial) {
      var tip = partial ? HP_TIP : TIP;
      var xs = edge(from, y0), xr = edge(to, y1), xc = xr + TIP + 10;
      var p = el('path', {
        d: 'M ' + r1(xs) + ' ' + r1(y0) + ' C ' + r1(xs + 34) + ' ' + r1(y0) + ', ' + r1(xs + 34) + ' ' +
           r1(y1) + ', ' + r1(xc) + ' ' + r1(y1) + ' L ' + r1(xr + tip) + ' ' + r1(y1),
        fill: 'none', stroke: color[s], 'stroke-width': STROKE,
        'marker-end': 'url(#cd-' + (partial ? 'hp-' : 'ah-') + s + ')'
      });
      if (DASH[s]) p.setAttribute('stroke-dasharray', DASH[s]);
      svg.appendChild(p);
      return p;
    }

    rows.forEach(function (r) {
      var m = mid(r.el), s = r.status, path;
      if (r.note) {
        var g = el('g', {});
        g.appendChild(el('circle', { cx: right + 16, cy: r1(m), r: 7, fill: noteFill, stroke: color[s], 'stroke-width': 1.4 }));
        var i = el('text', { x: right + 16, y: r1(m + 4), 'text-anchor': 'middle', 'font-size': 11,
          'font-weight': 'bold', fill: color[s] });
        i.textContent = 'i';
        g.appendChild(i);
        svg.appendChild(g);
        path = g.firstChild;
      } else if (r.fork) {
        /* a bracket from the box before the choice: a trunk down the gutter and a branch
           into each box of the fork, the farthest first, so a nearer branch's line lies on
           top where they share the trunk */
        var y0 = r.from ? r.from.bot - 4 : m, xs = edge(r.from, y0), tx = right + 18, k = 6;
        r.fork.slice().reverse().forEach(function (b) {
          var y1 = (b.top + b.bot) / 2, s1 = b.status;
          var p = el('path', {
            d: 'M ' + r1(xs) + ' ' + r1(y0) + ' L ' + (tx - k) + ' ' + r1(y0) + ' Q ' + tx + ' ' + r1(y0) + ' ' +
               tx + ' ' + r1(y0 + k) + ' L ' + tx + ' ' + r1(y1 - k) + ' Q ' + tx + ' ' + r1(y1) + ' ' +
               (tx - k) + ' ' + r1(y1) + ' L ' + r1(right + TIP) + ' ' + r1(y1),
            fill: 'none', stroke: color[s1], 'stroke-width': STROKE, 'marker-end': 'url(#cd-ah-' + s1 + ')'
          });
          if (DASH[s1]) p.setAttribute('stroke-dasharray', DASH[s1]);
          svg.appendChild(p);
          path = p;
        });
      } else {
        var y0 = r.cross && r.from ? r.from.bot - 4 : m - 9;
        var y1 = r.cross && r.to ? r.to.top + 4 : m + 9;
        path = arrow(r.from, y0, r.cross ? r.to : r.from, y1, s, r.partial);
        if (r.partial && r.fails) {
          /* the arrow takes no pointer; a wider invisible copy carries the tooltip */
          var hit = el('path', { d: path.getAttribute('d'), fill: 'none', stroke: 'transparent',
            'stroke-width': 10, 'pointer-events': 'stroke' });
          var t = el('title', {});
          t.textContent = r.fails;
          hit.appendChild(t);
          var pass = r.el;
          hit.addEventListener('pointerenter', function () { if (pass._set) pass._set(true); });
          hit.addEventListener('pointerleave', function () { if (pass._set) pass._set(false); });
          svg.appendChild(hit);
        }
      }
      if (!path) return;
      hover(r.el, path, r.partial ? 'url(#cd-hp-' + s + ')' : null);
    });
  }

  /* the pointer anywhere on a pass, its explanation included, thickens its arrow; the
     listeners are bound once per pass and act on whichever path the last layout drew */
  function hover(pass, path, harpoonEnd) {
    pass._arrow = { path: path, end: harpoonEnd };
    if (pass._hover) return;
    pass._hover = true;
    function set(hot) {
      var a = pass._arrow;
      if (!a || !a.path.isConnected) return;
      a.path.setAttribute('stroke-width', a.path.tagName === 'circle' ? (hot ? 2.4 : 1.4) : (hot ? STROKE_HOT : STROKE));
      if (a.end) a.path.setAttribute('marker-end', hot ? a.end.replace(')', '-h)') : a.end);
    }
    pass._set = set;
    pass.addEventListener('pointerenter', function () { set(true); });
    pass.addEventListener('pointerleave', function () { set(false); });
  }

  /* runs: once per frame at most, for whichever page is current */

  var queued = false;
  function schedule() {
    if (queued) return;
    queued = true;
    requestAnimationFrame(function () {
      queued = false;
      var root = document.getElementById('compiler');
      if (!root) return;
      tabs(root);
      stages(root);
      layout(root);
    });
  }

  document.addEventListener('site:render', schedule);
  /* a fold: toggle does not bubble, so it is caught on the way down */
  document.addEventListener('toggle', function (e) {
    if (e.target.closest && e.target.closest('#compiler')) schedule();
  }, true);
  window.addEventListener('resize', schedule);
  /* the arrows take their colours from the stylesheet, which has a set per theme */
  if (window.matchMedia) {
    var dark = window.matchMedia('(prefers-color-scheme: dark)');
    if (dark.addEventListener) dark.addEventListener('change', schedule);
  }
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(schedule);
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', schedule);
  else schedule();
})();
