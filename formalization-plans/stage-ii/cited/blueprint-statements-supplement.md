# 指示書 NB-W4：ブループリントの主張の一行・本論文の補足・v 降下の依存・BS の目次（紙）

作成：2026-11-18（調整役）。決定：ユーザー（11-18「okです。5の補足と9もやりましょう」）。レーン：⑧（worktree `../SerrePositivity-cited`、`pwd` を確かめ、始める前に `git merge main`）。紙だけ、Lean の変更・ビルド・鍵の使用なし。凍結中の `exposition/` と生成器（`blueprint/scripts/`）は読むだけ。証拠は git の外、目録だけコミット。報告は `report-clmst-coverage.md` に節「NB-W4」を続け、現在地を更新。段ごとにコミットし、段 4 は塊ごとにコミットする。全部終わったら止まる。

今のブループリント（http://127.0.0.1:8790/、生成物は `blueprint/SerreBlueprint/`）では、各項目のカードの頭が対応表の照合の理由（「原典 PDF p.15 …、型に含まれない」など）で、主張そのものが書かれていない項目が多い。これを埋めるのが段 4。段 1〜3 は小さい。

## 段 1　BS の目次

- `research/bs-coverage/toc.md` を作る（版・SHA-256 と、節番号 → 節の題の表）。形は `research/bs17-coverage/toc.md` に合わせる（生成器は `| 番号 | 題 |` の行を読む）。題は原典（著者版 PDF）の節の題そのまま（英語）。

## 段 2　本論文の補足（項目に対応しない文章）

- 入力：`exposition/ja/exposition-ja.tex` の「はじめに」・§1「主張と帰着」・§2「証明の方針」と、付録 B 以降（先行研究との関係、拡大すると高次の項が消える理由、λ-平坦を主役にした整理の検討、K 理論の降下の構造、ほか）。付録 A（引用した結果と形式化の状況）は対応表と重なるので写さない。
- §1・§2 のうち本論文の項目（`research/paper-coverage/items.csv`）に振れる段落は、NB-W2 と同じく `notes/<項目番号>.md`・`notes/<節番号>.md` に足す。
- 振れない文章（方針の説明、付録）は `research/paper-coverage/notes/supplement/<二桁の順番>-<slug>.md` に、元の節・付録ごとに一ファイル。一行目は `# <題>`、本文の形は NB-W2 と同じ（`## 見出し`、`\( \)`・`\[ \]`、追跡用のコメントとアンカー）。調整役が、部「本論文」の末尾に「補足」の章としてこの順で出す。
- 付録に「未確認」「精密ではない」と書かれた議論は、その断り書きごと写す。「2026-10-13 時点」など状態を述べる文は写さず、README に一覧にする。
- NB-W2 の保留 22 ブロックのうち、補足に置けば収まるものはここへ移し、issues から消す。

## 段 3　v 降下の部の依存

- 今の部「v 降下」（`blueprint/scripts/gen_cited.py` の `ROUTES['vdescent']`）は、BS17・BM18・Rydh のうち review が none でない 49 項目を載せ、辺は各 `edges.csv`（PDF の引用）から取っている。目標 BS17 Theorem 4.1 (i) からたどっても、本体の経路が読めない。
- `research/bs17-coverage/route-edges.csv`（列：`source,number,depends_on_source,depends_on_number,evidence`）を作る。本体の経路（⑥ の 2f〜2i：`SerrePositivity/AlgebraicGeometry/`、BM18 Proposition 4.8 の経路 B を通る）で、49 項目のうち「どの項目の宣言が、どの項目の宣言を使って作られているか」を、宣言の定義・証明の中の参照から読む（静的に、ソースで）。`evidence` は宣言名とファイル:行。対応する項目が 49 の外なら書かない。
- 目標 4.1 から route-edges でたどって届かない項目があれば、README に一覧にする（部に載せ続けるかは調整役が決める）。

## 段 4　主張の一行

- 対象：review の状態が none でない項目。本論文 58、CLMST 30、BS 77、BS17 11、BM18 23、Rydh 15、Kerodon 第 1〜10 章 1,336（計 約 1,550）。
- 出力：各 `research/<文献>-coverage/statements.csv`（列：`number,statement_ja`）。`statement_ja` は、その項目の主張を日本語で一〜三文に述べたもの。数式は `\( \)`。定義は「何を定義するか」、定理は仮定と結論。原典の本文の写し・逐語訳にはしない（自分の言葉で要約する）が、主張の中身は原典どおりに（仮定を落とさない、一般性を変えない）。原典を読んで書く（Kerodon は Tag のページ、他は PDF）。題（`title`・`title_ja`）や review の理由から推測して書かない。
- 本体の宣言との差（特別な場合だけ、など）は review の理由に既にあるので、ここには書かない。主張は原典の側。
- 順番：v 降下の 49 → 本論文 → CLMST → BS → Kerodon（第 1 章から、章ごとにコミット）。Kerodon は量が多いので、章ごとに止まらず続けてよいが、第 4 章が終わった所で一度報告を更新する。
- 原典が読めない・主張が一〜三文に収まらない項目は、空のままにして `statements-issues.md` に理由を書く。
- 調整役が、カードの一行目の下にこの文を出すよう生成器を直す（`statements.csv` があれば読む）。

## 止まるところ

- `items.csv` に無い番号を作らない。review の状態・宣言は変えない（誤りに気づいたら issues に所見）。
- Kerodon の review に行のない 531 項目（Remark・Example など、照合の対象外）は対象外。第 11 章（付録）も対象外。
