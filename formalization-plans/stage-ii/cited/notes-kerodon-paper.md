# 指示書 NB-W2：解説の原稿を増やす（Kerodon 第 2〜4 章と本論文、紙）

作成：2026-11-18（調整役）。決定：ユーザー（11-18「okです」）。レーン：⑧（worktree `../SerrePositivity-cited`、`pwd` を確かめ、始める前に `git merge main`）。紙だけ、Lean の変更・ビルド・鍵の使用なし。証拠は git の外、目録だけコミット。報告は `report-clmst-coverage.md` に節「NB-W2」を続け、現在地を更新。段ごとにコミットし、二つ終わったら止まる。

NB-W1（Kerodon 第 1 章、`research/kerodon-coverage/notes/`）の形を使う。原稿は生成器（`blueprint/scripts/gen_kerodon.py` の `note_body`）がノードの本文に入れる。規則は `notes/README.md` のとおり：`<項目番号>.md`（冒頭は題・Tag・照合先、本文は `## 見出し` と段落）、節の導入は `<節番号>.md`、文言は元のまま、数式は `\( \)`・`\[ \]` のまま、原典の本文は写さない。

## 段 1　Kerodon 第 2〜4 章（と、その先に当たる分）

- 入力：NB-W1 で第 1 章の外として `notes/issues.md` に保留した 47 ブロック（coherent nerve＝第 2 章、空間の ∞ 圏＝第 3 章、join・slice＝第 4 章 など）と、`exposition/ja/infinity/t-06-fiber-products.html`〜`t-15-yoneda.html`（凍結中、読むだけ）。
- 各段落を Kerodon の項目番号（`research/kerodon-coverage/items.csv`・`item-tags.csv` に実在するもの）に振り、`notes/<番号>.md` に写す。番号が決まらない導入・つなぎは節の原稿に。第 5 章以降に当たる段落（straightening・Yoneda など）も、項目が決まるものは同じ形で置く。
- NB-W1 の issues の所見（一段落が複数項目にまたがる、表の分割、review にない項目）は同じ規則で処理し、新しい所見だけ `issues.md` に足す。保留から移したブロックは issues から消し、README の行き先の表を更新する。
- review にない項目の原稿（今の生成器では使われない）は README に一覧にする（調整役が生成器を items.csv 起点に直す材料）。

## 段 2　本論文

- 入力：`exposition/ja/exposition-ja.tex`（§3〜§9・付録、凍結中、読むだけ）。
- 出力：`research/paper-coverage/notes/<項目番号>.md`（本論文の `items.csv` の番号：定理・補題・式など）と、節の導入 `<節番号>.md`。TeX は Markdown に直す（数式は `\( \)`・`\[ \]`、`\cref` などの参照は表示文言に、環境は `## 見出し`）。解説のどの段落がどの項目の説明かで振る。解説が論文の番号と別の構成（§3 共通理論、§4 長さ代数 …）で書かれている所は、対応する論文の項目に振り、振れない段落は `issues.md` に全文保留して理由を書く。
- 付録 A（引用・状態・実装の対応）は対応表と重なるので写さない（README にその旨）。
- README（規則と行き先の表）と issues.md（TeX → Markdown で困ったもの、振れなかった段落）。
