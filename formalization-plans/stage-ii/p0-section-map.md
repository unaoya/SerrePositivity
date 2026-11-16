# P⁰ の節の地図：DAG XIII・NS の対応表と、節の閉包（紙）

作成：2026-11-16 夕（調整役）。決定：ユーザー（11-16「okです」、方針は `p0-plan-draft.md` §6）。

## 0. 目的

計画の単位は文献の節（`p0-plan-draft.md` §6）。P⁰（DAG XIII Constr 2.2.6）への依存をたどって行き当たる節を、文献ごとに項目として全部挙げ、依存の順に並べる。これが段階の計画と進み具合の物差しになる。

## 1. ⑤a：DAG XIII と NS の対応表（新設）

- 置き場所：`research/dag13-coverage/`・`research/ns-coverage/`。形は HA の対応表（`research/ha-coverage/README.md`）と同じ：`toc.md`（節・小節の見出し）、`items.csv`（列 `number,kind,title,section,status,declarations,reason,confidence,lean_citations,plan_citations,kerodon,goal`、`kerodon` の列は他文献の同じ内容の番号を `HA 6.1.6.7` のように書いてよい）、`review/` に照合の結果。
- 範囲：**論文全体**の見出しと番号つきの全項目（HA の表と同じく本全体）。照合（status・declarations・reason）は、P⁰ に至る節（DAG XIII §1.1・§2.1・§2.2、NS I.1・I.3・III.1・IV.1 など）を先に、その後に残り。
- 版：DAG XIII は 2011 年の版（段 0 の報告で照合した版）、NS は arXiv:1707.01799v2。toc.md の冒頭に記録する。
- **文献の略号の登録**：`research/bibliography.json` に `DAGXIII`・`NS` を足し、`scripts/refactor/bulk_citation_registry.py` で `SerrePositivity/Util/Citation.lean` の登録を作り直す。対象ビルド（`Util/Citation` とそれを import するもの）は共有の鍵 `--class impl` で。これだけが Lean の変更。

## 2. ⑤d：HA・HTT・Kerodon の側の節の閉包

- 出発点：DAG XIII §2.2（Constr 2.2.6 とその前提）と NS の P⁰ に関わる節が引く HA・HTT・Kerodon の番号。⑤a の対応表ができる前でも、原典から直接拾ってよい。
- たどり方：閉包に入った節について、その節の定義・主張・証明が引く番号と、節の中の項目の前提を拾い、その番号を含む節を閉包に加える。これを繰り返す。節の中は全項目を作る前提なので、一項目でも要れば節ごと入る。
- 出力：`research/p0-lurie/section-closure/sections.csv`（列 `source,section,title,item_count,own,mathlib,partial,none,reached_from,reason`）と `edges.csv`（節 → 節、根拠の番号）、依存の順（トポロジカル順）の一覧 `order.md`。状態の内訳は既存の対応表から（HA・HTT・Kerodon）。
- **止める条件**：閉包が 150 節を超えたら、その時点の表をコミットして報告して止まる（大きさを見て進め方を決める）。

## 3. 規則

- 紙だけ（§1 の略号の登録を除く）。Lean の追加・ビルドはしない。
- 既存の対応表（HA・HTT・Kerodon の review）は書き換えない。食い違いを見つけたら報告に書く。
- それぞれ main（0bdc68cee 以降）から枝を切り、報告をコミットしたら止まる。調整役が二つを合わせて節の一覧と HTML の地図にする。
