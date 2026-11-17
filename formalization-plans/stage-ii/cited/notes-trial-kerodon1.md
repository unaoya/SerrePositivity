# 指示書 NB-W1：ブループリントの本文の試し（Kerodon 第 1 章、紙）

作成：2026-11-17（調整役）。決定：ユーザー（11-17「やりましょう」）。レーン：⑧（worktree `../SerrePositivity-cited`、枝 `research/cited-coverage`。`pwd` を確かめてから始める）。

## 0. 目的

ブループリント（`blueprint/`）のノードの本文には、いま対応表の「照合の理由」だけがある。数学の解説は `exposition/ja/infinity/`（凍結中）にある。将来 exposition をブループリントに一本化するので、解説を**生成器が読む原稿**として置く形を、Kerodon 第 1 章だけで試す。目的は設計の判断材料（粒度・置き場所・Verso への変換で困るもの）を得ること。設計は保留中なので、ここで決めた形は仮。

## 1. 入力

- 解説：`exposition/ja/infinity/t-01-definitions.html`〜`t-05-fibrations.html`（第 III 部 1〜5 章。単体的集合と quasicategory の定義、Kan 複体の単体的圏、homotopy coherent nerve、join とスライス、fibration）。読むだけで、exposition は書き換えない（凍結）。
- 対応表：`research/kerodon-coverage/review/ch1.csv`（第 1 章の 180 項目）、`item-tags.csv`（項目 → Tag）、`toc.md`（節の見出し）。
- 今の生成器：`blueprint/scripts/gen_kerodon.py`（ノードの形）。生成器は変えない（調整役が直す）。

## 2. 出力

`research/kerodon-coverage/notes/` に次を置く。
- `1.x.y.z.md`：Kerodon の項目番号ごとの解説の原稿。t-01〜t-05 の本文を、どの段落がどの項目（定義・定理・例）の説明かで切り分けて写す。Markdown。数式は KaTeX の `\( \)`・`\[ \]` のまま、Lean の宣言名はバッククォートでそのまま。原典（Kerodon）の本文は写さない（Tag へのリンクだけ）。文言は exposition のまま（直さない。明らかな誤りは `issues.md` に書く）。
- `1.x.md`・`1.x.y.md`：項目に対応しない「節の導入・つなぎ」の段落。
- `README.md`：原稿の規則（ファイル名、形、何を含めないか）、t-01〜t-05 の各段落がどこへ行ったかの表（`段落の先頭の数語 → ファイル`）、どこにも置けなかった段落の一覧とその理由。
- `issues.md`：試して分かったこと。**粒度**（複数の項目をまとめて説明している段落をどう切ったか、切れなかったもの）、**置き場所**（`research/<文献>-coverage/notes/` でよいか、research の規則「文献と Lean を引く」に合うか）、**Verso への変換で困るもの**（表、図、`<div class="box">` の囲み、`<pre>` の図、数式の環境、ページ間リンク）を、例を挙げて一つずつ。

## 3. 規則

紙だけ。Lean・ビルドなし。exposition・対応表・生成器は書き換えない。証拠が出れば git の外（`~/serre-evidence/cited/notes-kerodon1/`）、目録だけコミット。報告は `report-clmst-coverage.md` に続けて節「NB-W1」を書き、先頭の現在地を更新。コミットしたら止まる。
