# Codex 作業指示書 BS-DOC1：BS の docstring に論文の番号を書く

作成：2026-11-07（段階 II の調整役）。宛先：⑤ BS 実装の Codex（BS-W11 の前に行う）。検収：調整役。
決定（11-07、ユーザー）：BS のコードの docstring に、Bhatt–Scholze "Prisms and prismatic cohomology" の番号（定理・命題・補題・定義など）を書く。

## 0. 材料

- 対応表：`research/bs-coverage/items.csv`（論文の 211 項目。列 `number`・`kind`・`status`・`declarations` など）。`declarations` に、その項目に当たる本体の宣言が `名前 @ path:line` で並んでいる。本体（`SerrePositivity/`）の宣言は 184 個（71 項目）で、そのうち docstring に番号があるのは 63 個（11-07 時点）。
- 対応表は調査役（Claude）が宣言名・docstring・設計書で照合したもので、**Lean を動かしての確認はしていない**。番号を書く前に、宣言の主張が論文の項目と合っているかを確かめる。
- 論文は著者版（`paper/refs/BS-prisms-author.pdf`）。番号は著者版のもの。
- docstring の書き方は README の Conventions（日本語の 概要／方針／規約／使われ方）。

## 1. 書き方（統一の形）

- 項目に当たる宣言の docstring の**概要の行の末尾**に、`（BS 著者版 <種類> <番号>）` と書く。種類は論文の語をそのまま英語で書く（Definition・Theorem・Proposition・Lemma・Corollary・Construction・Remark・Example・Notation・Variant）。
  - 例：`単項商の perfectoid 化の核の mod pᴺ 像は冪等である（BS 著者版 Remark 10.7）。`
- 特別な場合だけを示す宣言は、`（BS 著者版 Lemma 3.7 (1) の向き付き prism の場合）` のように、限る内容を書く。どの場合に限るかは `items.csv` の `note` を出発点にし、主張を読んで確かめる。
- 項目の一部（(1)・(2) などの小項目、第一文など）だけに当たるものは、その部分を書く（例：`Corollary 7.3 の第一文`）。
- §1（序論）の定理は、本文の節の番号を主にし、序論の番号を添える（例：`（BS 著者版 Theorem 7.4、序論の Theorem 1.12）`）。
- 既存の引用は、上の形にそろえる。「BS Rem 7.15」「BS Thm 7.14」「BS 著者版 Thm 7.14」「文献名なしの Lemma 4.8」などを `BS 著者版 Remark 7.15` の形にする。文献名なしの番号は、BS のものか他の文献のものかを確かめてから直す（他の文献なら触らない）。
  - 印刷版のページなど、今ある付記は残してよい。
- **補助の補題**（論文の項目そのものではないもの）には、宣言ごとの番号は付けなくてよい。代わりに、**ファイルの module docstring** に、そのファイルが論文のどの節・項目のためのものかを書く（例：`BS 著者版 §7、Theorem 7.14 の証明（Remark 7.15 の構成）のための補題`）。BhattScholze の 144 本のうち 34 本は項目の番号がどこにもないので、全ファイルの module docstring を確かめる。
- 対象のディレクトリ：`SerrePositivity/BhattScholze/` の全体と、BS の項目に当たる宣言を含むほかのファイル（`items.csv` で拾う。CommutativeAlgebra の 7、HomologicalAlgebra の 1、CLMST の 1 など）。

## 2. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 1 | 対応の確認：`items.csv` の本体の宣言 184 個について、主張が論文の項目と合っているかを `#check` で型を見て確かめ、`research/bs-coverage/doc1-check.csv`（`number`・`declaration`・`verdict`（ok・fix・unsure）・`scope`（全体／特別な場合の内容）・`reason`）に書く。合わないものは書き換えの対象から外す。既存の引用のまちまちな書き方の一覧（形ごとの件数）も作る | **停止点 1**：確認の結果と、書き換える件数の見込み。調整役が確かめる |
| 段 2 | 書き換え：§1 の形で docstring と module docstring を書き換える。**docstring とコメントの行だけを変え、Lean のコードは変えない**。変更がコメントと docstring だけであることを、差分を解析するスクリプトで確かめる（`/--`〜`-/`、`/-!`〜`-/`、`--` の外の行が変わっていないこと） | 停止点 2：書き換えた件数、スクリプトの結果、対象のビルド |
| 段 3 | ビルド：書き換えたモジュールと直接の importer だけを小さなビルドで確かめる。BS を import する下流（CLMST・Paper など）の全ビルドは、調整役の合図で一回 | 停止点 3：取り込み |

- 段 1 から段 2 は、停止点 1 で調整役が承認してから進む。
- 段 2 から段 3 は、「変更がコメントと docstring だけ、対象のビルドが通る」なら、報告して承認を待たずに進んでよい。

## 3. 規則

1. Lean のコード（宣言の名前・型・本文、import、attribute）は変えない。docstring とコメントだけ。
2. drafts（`formalization-plans/bhatt-scholze/drafts/`）は対象外（調整役が別に直す）。
3. worktree は main から切る（`../SerrePositivity-bs-impl`、枝 `math/bs-impl`）。main の作業木では作業しない。取り込みは調整役。
4. ビルドは小さなものだけ（`ps -axo command= | grep '[l]ake build'` と `scripts/refactor/with_build_lock.sh --wait 0`）。下流の全ビルドは調整役の合図で。
5. F-2 の改名表 `scripts/refactor/targets/f-namespace-map.json` で名前空間が変わった宣言は、新しい名前で扱う。

## 4. 追記（2026-11-07、調整役）：停止点 1 の承認

**承認**：照合（184 行：ok 149・fix 34・unsure 1、`research/bs-coverage/doc1-check.csv`）と段 2 の範囲（45 ファイル・136 宣言：新規 80、既存の確認 56）。段 2 に進んでよい。§2 のとおり、変更が docstring とコメントだけで対象のビルドが通るなら、報告して段 3 へ進んでよい。

1. **fix の扱い**：照合で「項目そのものではなく補助・別の帰結」とした宣言には、宣言ごとの番号を付けない。代わりに module docstring に、そのファイルが論文のどの項目のための補助かを書く（§1 の補助の補題の規則）。対応の誤り（例：Def 1.4 の候補、Rem 10.7 の振り分け、16.9 の抜き出しの誤り）は、doc1-check.csv の `reason` のとおりに扱う。
2. **unsure（8.2、E3 の perfd 欄）**：欄の型は普通の R 代数を受け取る界面で、Δ の完全化の式は型に現れない。欄の docstring には、定義そのものとしてではなく「何を受け取る欄か」として書く。例：`（BS 著者版 Definition 8.2 の perfectoid 化を受け取る E3 の欄。Lemma 8.4 とあわせて引用）`。E3 のほかの欄も同じ扱いにする（limitCone は Prop 8.5、excision は Cor 8.12、universal は Cor 8.14、integral は Thm 10.11）。
3. 取り込みの後、調整役が `research/bs-coverage/items.csv` と形式化マップに doc1-check.csv の訂正を反映する（Codex は items.csv を編集しない）。
