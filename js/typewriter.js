/* Types out the homepage tagline, one line after another.
 *
 * Every line is split into a visible typed part and an invisible remainder,
 * so the box has its final size from the start and nothing jumps around.
 */
(function () {
  'use strict';

  const TYPE_MS = 45;
  const LINE_PAUSE_MS = 450;

  function start(box) {
    const lines = [...box.querySelectorAll('.typewriter-line')].map((line) => {
      const chars = Array.from(line.textContent);
      line.textContent = '';
      const typed = document.createElement('span');
      typed.className = 'typewriter-typed';
      const rest = document.createElement('span');
      rest.className = 'typewriter-rest';
      rest.textContent = chars.join('');
      line.append(typed, rest);
      return { line, typed, rest, chars };
    });
    if (!lines.length) return;

    if (window.matchMedia('(prefers-reduced-motion: reduce)').matches) {
      lines.forEach((l) => { l.typed.textContent = l.chars.join(''); l.rest.textContent = ''; });
      box.classList.add('typewriter-done');
      return;
    }

    let row = 0;
    let col = 0;
    const tick = () => {
      const l = lines[row];
      l.line.classList.add('typing');
      col++;
      l.typed.textContent = l.chars.slice(0, col).join('');
      l.rest.textContent = l.chars.slice(col).join('');
      if (col < l.chars.length) {
        setTimeout(tick, TYPE_MS);
        return;
      }
      if (row === lines.length - 1) {
        box.classList.add('typewriter-done');
        return;
      }
      l.line.classList.remove('typing');
      row++;
      col = 0;
      setTimeout(tick, LINE_PAUSE_MS);
    };
    setTimeout(tick, 400);
  }

  function init() {
    document.querySelectorAll('.typewriter-text').forEach(start);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
