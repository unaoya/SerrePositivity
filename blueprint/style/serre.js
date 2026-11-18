// SerrePositivity ブループリント：目次を木にする。
// Verso は章の中の節を目次の下に別の枠で出し、下の階層のページでは全体の目次を畳む。
// ここでは全体の目次を開いたままにし、章の直下にその節を並べる（今いる章は開く。▸ で開閉）。
// 章 → 節の表 window.SP_TOC は style_site.py が作る（serre-toc.js）。
document.addEventListener("DOMContentLoaded", () => {
  const root = document.getElementById("--verso-manual-toc-----bookRoot");
  if (root && !root.checked) root.checked = true;
  const here = decodeURIComponent(location.pathname);
  const pathOf = (a) => decodeURIComponent(new URL(a.href).pathname);
  const toc = window.SP_TOC || {};
  let best = null, bestLen = 0;
  const consider = (a) => {
    const p = pathOf(a);
    if (p.length > 1 && here.startsWith(p) && p.length > bestLen) { best = a; bestLen = p.length; }
  };
  document.querySelectorAll("#toc .split-toc.book tr").forEach((tr) => {
    const a = tr.querySelector("a[href]");
    if (!a) return;
    consider(a);
    const kids = toc[(a.getAttribute("href") || "").split("#")[0]];
    if (!kids || !kids.length) return;
    const open = here.startsWith(pathOf(a));
    const btn = document.createElement("button");
    btn.className = "sp-caret"; btn.type = "button";
    btn.setAttribute("aria-expanded", String(open));
    btn.setAttribute("aria-label", "節を開閉");
    const row = document.createElement("tr");
    row.className = "sp-children"; row.hidden = !open;
    const td0 = document.createElement("td"); td0.className = "num";
    const td = document.createElement("td");
    const ul = document.createElement("ul");
    kids.forEach(([href, title]) => {
      const li = document.createElement("li");
      const k = document.createElement("a");
      k.setAttribute("href", href); k.textContent = title;
      li.appendChild(k); ul.appendChild(li); consider(k);
    });
    td.appendChild(ul); row.appendChild(td0); row.appendChild(td);
    tr.after(row);
    a.parentElement.classList.add("sp-has-children");
    a.before(btn);
    btn.addEventListener("click", () => {
      row.hidden = !row.hidden;
      btn.setAttribute("aria-expanded", String(!row.hidden));
    });
  });
  if (best) { best.classList.add("sp-current"); best.scrollIntoView({ block: "center" }); }
});
