#!/usr/bin/env python3
"""章ごとの HTML を、claude.ai Artifact 公開用の 1 ページにまとめる。

使い方: python3 build_artifact.py OUT_DIR KATEX_DIR
  KATEX_DIR には katex.min.css と fonts/*.woff2 を置いておく。
  OUT_DIR に index.html を書き出す（フォントは KATEX_DIR/fonts を files として公開する）。

変換の内容:
  - 目次（index.html）を先頭に、目次の表に現れる順で各ページを <section> として連結する
  - ページ間リンク（xx.html）はページ内リンク（#sec-xx）に、index.html は #top に置き換える
  - リポジトリ内のファイルへのリンク（../ で始まるもの）は文字だけ残す
  - style.css・KaTeX の CSS・各ページ固有の <style> を一つにまとめてインラインにする
"""
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent


def main_inner(html: str) -> str:
    m = re.search(r"<main>(.*)</main>", html, re.S)
    return m.group(1) if m else html


def page_styles(html: str) -> str:
    return "\n".join(re.findall(r"<style>(.*?)</style>", html, re.S))


def rewrite_links(body: str) -> str:
    # リポジトリ内ファイルへのリンクは文字だけにする
    body = re.sub(r'<a href="\.\./[^"]*">(.*?)</a>', r"\1", body, flags=re.S)
    body = re.sub(r'href="index\.html"', 'href="#top"', body)
    body = re.sub(r'href="([A-Za-z0-9_-]+)\.html(?:#[^"]*)?"', r'href="#sec-\1"', body)
    return body


def main() -> None:
    out_dir = pathlib.Path(sys.argv[1])
    katex_dir = pathlib.Path(sys.argv[2])
    out_dir.mkdir(parents=True, exist_ok=True)

    index_html = (HERE / "index.html").read_text()
    index_body = main_inner(index_html)
    order = []
    for stem in re.findall(r'href="([A-Za-z0-9_-]+)\.html', index_body):
        if stem != "index" and stem not in order and (HERE / f"{stem}.html").exists():
            order.append(stem)

    styles = [(HERE / "style.css").read_text(), (katex_dir / "katex.min.css").read_text()]
    sections = []
    for stem in order:
        html = (HERE / f"{stem}.html").read_text()
        styles.append(page_styles(html))
        body = main_inner(html)
        body = re.sub(r'<nav class="top">.*?</nav>', "", body, flags=re.S)
        body = rewrite_links(body)
        sections.append(
            f'<section id="sec-{stem}" class="chapter">\n{body}\n'
            f'<p class="backtop"><a href="#top">目次へ戻る</a></p>\n</section>'
        )

    extra_css = """
@media (prefers-color-scheme: dark) { :root:not([data-theme="light"]) { color-scheme: dark; } }
:root[data-theme="dark"] { color-scheme: dark; }
section.chapter { border-top: 2px solid var(--rule); margin-top: 3.5rem; padding-top: 1.2rem; }
.backtop { margin-top: 2rem; font-size: 0.9rem; }
.katex-display { overflow-x: auto; overflow-y: hidden; padding-block: 0.2rem; }
"""
    page = f"""<title>∞ 圏基盤の解説</title>
<style>
{chr(10).join(styles)}
{extra_css}
</style>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"></script>
<script>
document.addEventListener("DOMContentLoaded", function () {{
  if (window.renderMathInElement) {{
    renderMathInElement(document.body, {{delimiters: [
      {{left: "\\\\(", right: "\\\\)", display: false}},
      {{left: "\\\\[", right: "\\\\]", display: true}}]}});
  }}
}});
</script>
<main>
<div id="top">
{rewrite_links(index_body)}
</div>
{chr(10).join(sections)}
</main>
"""
    (out_dir / "index.html").write_text(page)
    print(f"wrote {out_dir / 'index.html'} ({len(page)} bytes, {len(order)} sections: {', '.join(order)})")


if __name__ == "__main__":
    main()
