// SerrePositivity ブループリント：目次の使い勝手の補い。
// Verso は下の階層のページで全体の目次を畳む。ここでは開いたままにし、今いる節に印を付けて見える位置に寄せる。
document.addEventListener("DOMContentLoaded", () => {
  const root = document.getElementById("--verso-manual-toc-----bookRoot");
  if (root && !root.checked) root.checked = true;
  const here = decodeURIComponent(location.pathname);
  let best = null, bestLen = 0;
  document.querySelectorAll("#toc .split-toc.book a[href]").forEach((a) => {
    const p = decodeURIComponent(new URL(a.href).pathname);
    if (p.length > 1 && here.startsWith(p) && p.length > bestLen) { best = a; bestLen = p.length; }
  });
  if (best) {
    best.classList.add("sp-current");
    best.scrollIntoView({ block: "center" });
  }
});
