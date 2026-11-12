#!/usr/bin/env python3
"""地図 research/bs-coverage/items.csv から、勉強ノートの項目の表を書き出す。

使い方: python3 build_items.py [--check]
  引数なし：各章の「原典の項目一覧」と 00-map.html の節ごとの表を書き換える。
  --check ：書き換えずに、生成結果と今の HTML が違えば差のある章を出して終了コード 1。

書き換える範囲:
  - 各章の <!-- items:begin --> 〜 <!-- items:end --> の間（「原典の項目一覧」の説明と表）
  - 各章の項目の見出し（h4.item）の確認のラベル（地図の status から。証明の囲みに data-supplemented があれば「補った筋あり」）
  - 00-map.html の <!-- sections:begin --> 〜 <!-- sections:end --> の間（節ごとの集計）
  印の外（本文・原典との差の評価）には触らない。印がまだない章は、初回だけ
  「原典の項目一覧」の見出しの直後の説明の段落と表を印で囲んでから置き換える。

items.csv の列の扱い:
  - title_ja は HTML としてそのまま入れる（KaTeX の \\( \\) や <code> を含んでよい）。空なら title（英語）。
  - note は「 ／ 」で区切り、作業の記録（「DOC1 照合…」「11-10 更新…」）の区切りを落として載せる。
  - declarations は「名前 @ パス:行 | …」。パスが今の作業木にない宣言はリンクなしで載せ、標準エラーに出す。
"""
import csv
import html
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ITEMS = ROOT / "research" / "bs-coverage" / "items.csv"

# 章のファイルと、その章が受け持つ原典の節
CHAPTERS = {
    "02-delta.html": [2],
    "03-prism.html": [3],
    "04-site.html": [4],
    "05-hodge-tate.html": [5, 6],
    "07-semiperfectoid.html": [7],
    "08-perfection.html": [8],
    "10-almost.html": [10],
}

# 原典の節の題（著者版の目次）
SECTIONS = {
    1: "序",
    2: "δ 環",
    3: "prism",
    4: "prismatic site と HT 比較の定式化",
    5: "標数 p の場合：HT 比較と結晶比較",
    6: "混標数の HT 比較",
    7: "semiperfectoid 環と混標数の perfection",
    8: "混標数の perfection：一般の場合",
    9: "étale 比較定理",
    10: "almost purity",
    11: "perfectoid 環の étale コホモロジー次元",
    12: "qrsp の Nygaard filtration",
    13: "[BMS19] との比較",
    14: "p 進 Tate 捻りと K 理論の奇数次消滅予想",
    15: "Nygaard filtration：相対の場合",
    16: "q 結晶コホモロジーと q de Rham コホモロジー",
    17: "AΩ との比較",
    18: "比較同型の一意性の判定法",
}

KIND = {
    "Definition": "Def", "Lemma": "Lemma", "Theorem": "Thm", "Proposition": "Prop",
    "Corollary": "Cor", "Remark": "Rem", "Example": "Ex", "Construction": "Constr",
    "Notation": "Not", "Warning": "Warn",
}

GOAL = {"required": "必要", "special": "一部必要", "not_required": "不要", "unknown": "未確定"}

# status → (表示, td の class)
STATUS = {
    "proved": ("済", "ok"),
    "proved_special": ("特別な場合", "part"),
    "parts_in_body": ("部品", "part"),
    "e3_input": ("界面", "todo"),
    "drafts": ("drafts", "todo"),
    "design_only": ("設計のみ", "todo"),
    "none": ("なし", "todo"),
}
STATUS_ORDER = ["proved", "proved_special", "parts_in_body", "drafts", "e3_input", "design_only", "none"]

NEEDED = ("required", "special")

LEGEND = (
    "判定：<b>必要性</b>は今の目標（E3 を原典の経路 A0〜A9 で消す）に要るか（<b>一部必要</b>＝項目の一部だけ要る）。"
    "<b>状況</b>は <b>済</b>＝本体に原典どおり（sorry なし）、<b>特別な場合</b>＝本体に特別な場合だけ、"
    "<b>部品</b>＝証明の主な部品は本体で主張の組み立ては未、<b>drafts</b>＝drafts に型だけ、"
    "<b>界面</b>＝E3 の欄として今は引用、<b>設計のみ</b>＝設計書だけ、<b>なし</b>＝どこにもない。"
)


def sort_key(number: str):
    return tuple(int(n) for n in number.split("."))


def section_of(row) -> int:
    return int(row["number"].split(".")[0])


def load_items():
    with open(ITEMS, newline="") as f:
        rows = list(csv.DictReader(f))
    rows.sort(key=lambda r: sort_key(r["number"]))
    for r in rows:
        if r["status"] not in STATUS:
            sys.exit(f"items.csv: 未知の status {r['status']!r}（{r['number']}）")
        if r["goal"] not in GOAL:
            sys.exit(f"items.csv: 未知の goal {r['goal']!r}（{r['number']}）")
    return rows


def clean_note(note: str) -> str:
    parts = [p.strip() for p in note.split("／")]
    keep = [p for p in parts if p and not p.startswith("DOC1 照合") and not re.match(r"\d+-\d+ (の)?更新", p)]
    return " ／ ".join(keep)


def render_declarations(decls: str, missing: list) -> str:
    out = []
    for d in filter(None, (s.strip() for s in decls.split("|"))):
        m = re.match(r"(.+?) @ (.+?)(?::(\d+))?$", d)
        if not m:
            out.append(f"<code>{html.escape(d)}</code>")
            continue
        name, path, line = m.groups()
        if path.startswith("SerrePositivity/BhattScholze/"):
            label = path[len("SerrePositivity/BhattScholze/"):]
        elif path.startswith("SerrePositivity/"):
            label = path[len("SerrePositivity/"):]
        elif path.startswith("formalization-plans/bhatt-scholze/drafts/"):
            label = "drafts/" + path[len("formalization-plans/bhatt-scholze/drafts/"):]
        else:
            label = path
        label = label.removesuffix(".lean") + (f":{line}" if line else "")
        if (ROOT / path).exists():
            loc = f'<a href="../../../{html.escape(path)}">{html.escape(label)}</a>'
        else:
            missing.append(f"{name} @ {path}")
            loc = html.escape(label)
        out.append(f"<code>{html.escape(name)}</code>（{loc}）")
    return "、".join(out)


def render_row(r, missing: list) -> str:
    head = f"{KIND.get(r['kind'], r['kind'])} {r['number']}"
    title = r.get("title_ja") or html.escape(r["title"])
    label, cls = STATUS[r["status"]]
    goal = GOAL[r["goal"]]
    goal_cls = "no" if r["goal"] == "not_required" else ""
    if r["status"] == "none" and r["goal"] == "not_required":
        label, cls = "—", "no"
    lean = render_declarations(r["declarations"], missing)
    note = html.escape(clean_note(r["note"]))
    body = "。".join(x for x in (lean, note) if x)
    gtd = f'<td class="{goal_cls}">{goal}</td>' if goal_cls else f"<td>{goal}</td>"
    return f'<tr><td>{head}</td><td>{title}</td>{gtd}<td class="{cls}">{label}</td><td>{body}</td></tr>'


def counts_line(rows) -> str:
    needed = [r for r in rows if r["goal"] in NEEDED]
    parts = []
    for s in STATUS_ORDER:
        n = sum(1 for r in needed if r["status"] == s)
        if n:
            parts.append(f"{STATUS[s][0]} {n}")
    return f"全 {len(rows)} 項目、うち目標に要るもの {len(needed)}（" + "、".join(parts) + "）。"


def chapter_block(rows, sections, missing) -> str:
    sel = [r for r in rows if section_of(r) in sections]
    name = "・".join(f"§{s}" for s in sections)
    lines = [
        "<!-- items:begin（build_items.py が research/bs-coverage/items.csv から生成。手で直さない） -->",
        f"<p>{name} の全項目。{counts_line(sel)}{LEGEND}"
        "Lean の所在は <code>SerrePositivity/BhattScholze/</code> からのパスと行（drafts は "
        "<code>formalization-plans/bhatt-scholze/drafts/</code> から）。</p>",
        '<div class="table-wrap"><table>',
        "<tr><th>項目</th><th>内容</th><th>必要性</th><th>状況</th><th>Lean・備考</th></tr>",
    ]
    lines += [render_row(r, missing) for r in sel]
    lines += ["</table></div>", "<!-- items:end -->"]
    return "\n".join(lines)


def sections_block(rows) -> str:
    chapter_of = {s: f for f, ss in CHAPTERS.items() for s in ss}
    head = "".join(f"<th>{STATUS[s][0]}</th>" for s in STATUS_ORDER)
    lines = [
        "<!-- sections:begin（build_items.py が research/bs-coverage/items.csv から生成。手で直さない） -->",
        "<p>原典の節ごとの項目数と、目標（E3 を消す）に要る項目の状況。状況の欄の意味は各章の「原典の項目一覧」と同じ。"
        "§1 は §2 以降の要約、§9 と §11〜§18 は今の目標の外で、章を置いていない。</p>",
        '<div class="table-wrap"><table>',
        f"<tr><th>節</th><th>題</th><th>項目</th><th>要る</th>{head}<th>章</th></tr>",
    ]
    total = {"all": 0, "needed": 0, **{s: 0 for s in STATUS_ORDER}}
    for sec, title in SECTIONS.items():
        sel = [r for r in rows if section_of(r) == sec]
        needed = [r for r in sel if r["goal"] in NEEDED]
        total["all"] += len(sel)
        total["needed"] += len(needed)
        cells = []
        for s in STATUS_ORDER:
            n = sum(1 for r in needed if r["status"] == s)
            total[s] += n
            cells.append(f'<td class="num">{n or ""}</td>')
        f = chapter_of.get(sec)
        ch = (f'<a href="{f}">{int(f[:2])}</a>' if f in NO_ITEMS_TABLE else f'<a href="{f}#items-{f[:2]}">{int(f[:2])}</a>') if f else "—"
        lines.append(
            f'<tr><td>§{sec}</td><td>{title}</td><td class="num">{len(sel)}</td>'
            f'<td class="num">{len(needed) or ""}</td>{"".join(cells)}<td>{ch}</td></tr>'
        )
    tc = "".join(f'<td class="num"><b>{total[s]}</b></td>' for s in STATUS_ORDER)
    lines.append(
        f'<tr><td colspan="2"><b>計</b></td><td class="num"><b>{total["all"]}</b></td>'
        f'<td class="num"><b>{total["needed"]}</b></td>{tc}<td></td></tr>'
    )
    lines += ["</table></div>", "<!-- sections:end -->"]
    return "\n".join(lines)


# 項目の見出しに付ける確認のラベル（地図の status から）
VERIFY = {
    "proved": ("Lean で確認", "v-ok"),
    "proved_special": ("一部 Lean で確認", "v-part"),
    "parts_in_body": ("一部 Lean で確認", "v-part"),
}
VERIFY_NO = ("未確認", "v-no")
VTAG_RE = re.compile(r'\s*<span class="vtag[^"]*">[^<]*</span>')
ITEM_RE = re.compile(r'<h4 class="item">(.*?)</h4>(.*?)(?=<h4 class="item">|<h2|<!-- items:begin|</main>)', re.S)
# 「原典の項目一覧」を置かない章（地図と重複するので外した。見出しのラベルだけ付ける）
NO_ITEMS_TABLE = {"02-delta.html", "03-prism.html", "04-site.html"}
NUM_RE = re.compile(r"(?:Definition|Def|Lemma|Remark|Rem|Example|Ex|Corollary|Cor|Proposition|Prop|Theorem|Thm|Warning|Warn|Construction|Constr|Notation|Not)\.?\s*(\d+\.\d+)")


def label_items(text: str, rows) -> str:
    """各項目の見出し（h4.item）に、地図の状態から確認のラベルを付け直す。補った筋の印（data-supplemented）があれば添える。"""
    status = {r["number"]: r["status"] for r in rows}
    order = ["proved", "proved_special", "parts_in_body"]

    def one(m):
        head = VTAG_RE.sub("", m.group(1)).rstrip()
        body = m.group(2)
        plain = re.sub(r"<[^>]+>", "", head)
        # 「Lemma 3.7 の後の段落」のような項目は、その番号の状態でなく Lean の囲みで判定する
        nums = [] if "段落" in plain else [n for n in NUM_RE.findall(plain) if n in status]
        if nums:
            st = [status[n] for n in nums]
            best = min(st, key=lambda s: order.index(s) if s in order else len(order))
            label, cls = VERIFY.get(best, VERIFY_NO)
        else:
            lean = re.search(r'<div class="box lean">(.*?)</div>', body, re.S)
            has = lean and "<code>" in lean.group(1) and "本体にない" not in lean.group(1)
            label, cls = ("Lean で確認", "v-ok") if has else VERIFY_NO
        tags = f' <span class="vtag {cls}">{label}</span>'
        if "data-supplemented" in body:
            tags += ' <span class="vtag v-supp">補った筋あり</span>'
        return f'<h4 class="item">{head}{tags}</h4>{body}'

    return ITEM_RE.sub(one, text)


def replace_marked(text: str, tag: str, block: str, fallback: re.Pattern, fname: str) -> str:
    pat = re.compile(rf"<!-- {tag}:begin.*?<!-- {tag}:end -->", re.S)
    if pat.search(text):
        return pat.sub(lambda _: block, text, count=1)
    if tag == "items" and fname in NO_ITEMS_TABLE:
        return text  # 項目の表を地図に任せた章（2026-11-12 から。状態は見出しのラベル）
    m = fallback.search(text)
    if not m:
        sys.exit(f"{fname}: 印も、初回に置き換える範囲も見つからない")
    return text[: m.start("body")] + block + text[m.end("body"):]


def main() -> None:
    check = "--check" in sys.argv[1:]
    rows = load_items()
    missing: list = []
    outputs = {}
    for fname, sections in CHAPTERS.items():
        path = HERE / fname
        text = path.read_text()
        num = fname[:2]
        fallback = re.compile(
            rf'<h2 id="items-{num}">[^<]*</h2>\s*(?P<body><p>.*?</table></div>)', re.S
        )
        outputs[path] = label_items(replace_marked(text, "items", chapter_block(rows, sections, missing), fallback, fname), rows)
    path = HERE / "00-map.html"
    fallback = re.compile(
        r"<h2>4\. 原典の節と形式化の状況</h2>\s*(?P<body><div class=\"table-wrap\"><table>.*?</table></div>)", re.S
    )
    outputs[path] = replace_marked(path.read_text(), "sections", sections_block(rows), fallback, "00-map.html")

    for m in sorted(set(missing)):
        print(f"警告：パスが作業木にない {m}", file=sys.stderr)
    stale = [p.name for p, t in outputs.items() if p.read_text() != t]
    if check:
        if stale:
            print("生成結果と違う：" + "、".join(stale))
            sys.exit(1)
        print("すべて最新")
        return
    for p, t in outputs.items():
        if p.read_text() != t:
            p.write_text(t)
    print("書き換え：" + ("、".join(stale) if stale else "なし"))


if __name__ == "__main__":
    main()
