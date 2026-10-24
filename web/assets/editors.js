/* a div.picker holds one .option per editor, each with a label which become a row
   of pills above the options. the chosen pill filters the option's content
   (without this script every option shows up vertically stacked). */
(function () {
  'use strict';

  var KEY = 'caraml-editor';

  function load() { try { return localStorage.getItem(KEY); } catch (e) { return null; } }
  function save(v) { try { localStorage.setItem(KEY, v); } catch (e) { /* private window */ } }

  function options(picker) {
    return Array.prototype.filter.call(picker.children, function (c) {
      return c.classList.contains('option');
    });
  }

  function show(picker, label) {
    var list = options(picker), sel = null;
    list.forEach(function (o) { if (o.getAttribute('label') === label) sel = o; });
    sel = sel || list[0];
    list.forEach(function (o) { o.classList.toggle('off', o !== sel); });
    Array.prototype.forEach.call(picker.querySelectorAll(':scope > .pills button'), function (b) {
      b.setAttribute('aria-pressed', String(b.textContent === sel.getAttribute('label')));
    });
  }

  function setup(picker) {
    if (picker.classList.contains('tabbed')) return;
    picker.classList.add('tabbed');
    var bar = document.createElement('div');
    bar.className = 'pills';
    bar.setAttribute('role', 'group');
    options(picker).forEach(function (o) {
      var b = document.createElement('button');
      b.type = 'button';
      b.textContent = o.getAttribute('label');
      b.addEventListener('click', function () {
        save(b.textContent);
        show(picker, b.textContent);
      });
      bar.appendChild(b);
    });
    picker.insertBefore(bar, picker.firstChild);
    show(picker, load());
  }

  function render() { Array.prototype.forEach.call(document.querySelectorAll('.picker'), setup); }

  document.addEventListener('site:render', render);
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', render);
  else render();
})();
