/* Turns "#email" links into a real mailto: link in the browser, so the address
 * never appears in the page HTML where scrapers collect it. */
(function () {
  'use strict';

  const address = ['bilalsarwar466', 'gmail.com'].join('@');

  function wire() {
    document.querySelectorAll('a[href$="#email"]').forEach((a) => {
      a.href = `mailto:${address}`;
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', wire);
  } else {
    wire();
  }
})();
