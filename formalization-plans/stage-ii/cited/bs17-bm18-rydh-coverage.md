# 指示書 CC-W3：BS17・BM18・Rydh の対応表（紙）

作成：2026-11-18（調整役）。決定：ユーザー（11-18「8 の次の BS などの作業をお願いしましょう」）。レーン：⑧（worktree `../SerrePositivity-cited`、`pwd` を確かめ、始める前に `git merge main`）。

## 0. 目的

⑥ スキーム論（11-18 に閉じた）が BS17 Thm 4.1 (i) と G-A6-1（BM18 Prop 4.8 の経路 B）を `SerrePositivity/AlgebraicGeometry/` に作った（2g-2・2h・2i、main 1fb2c6dcc・72bc75e8b）。その成果を文献の項目に結び、ブループリントの部と地図にするため、三つの文献の項目ごとの対応表を作る。宣言の単位の計測では AlgebraicGeometry の宣言のうちノードから届くものは 6% で、対応する表がないのが主な理由。

## 1. 対象と版（`research/bibliography.json`）

| 略号 | 文献 | 版 |
| --- | --- | --- |
| BS17 | Bhatt–Scholze, *Projectivity of the Witt vector affine Grassmannian* | arXiv:1507.06490v3 |
| BM18 | Bhatt–Mathew, *The arc-topology* | arXiv:1807.04725v4 |
| Rydh | Rydh, *Submersions and effective descent of étale morphisms* | arXiv:0710.2488v3 |

PDF はリポジトリにないので arXiv から取得して git の外（`~/serre-evidence/cited/sources/`）に置き、SHA-256 を toc.md に書く。リポジトリに PDF を入れない。

## 2. 対応表

置き場所：`research/bs17-coverage/`・`research/bm18-coverage/`・`research/rydh-coverage/`。形は `research/clmst-coverage/` と同じ（`toc.md`、`items.csv`（12 列、状態は review から）、`review/ch<N>.csv`（`number,status,declarations,reason,axioms,check,partial_kind`）、`edges.csv`（`number,depends_on,evidence_location,kind`）、`review/check/none-search.csv`、README に集計）。
- **全**番号つき項目（本論文や ⑥ が使う項目だけに限らない）。
- 状態の語と基準は `research/kerodon-coverage/codex-review.md` §8.1 と同じ（own・mathlib・both・partial（`partial_kind`）・interface・none）。⑥ が狭めた形（BS17 Thm 4.1 (i) の n = 1・E = O・affine・有限族、BM18 Prop 4.8 の構造層の場合）は `partial`（`special`）にし、差を理由に書く（⑥ の指示書 `stage-ii/scheme/scheme-w1.md` の 11-17 の追記、BS17 の残りの一般性は作らないと決めた）。
- 宣言の照合は、⑥ の報告（`scheme-w1-2g-2-report.md`・`scheme-w1-2h-report.md`・`scheme-w1-2i-report.md`、署名の紙 `scheme-w1-2g-2-residual-lemma-plan.md`・`scheme-w1-2i-route.md`）が挙げた宣言と原典の番号を起点に、`SerrePositivity/AlgebraicGeometry/`・`KST/SchemeLemmas/`・`CommutativeAlgebra/` などを読む。Stacks の Tag を経由するものは `external` の辺にする。
- BS の対応表（`research/bs-coverage/review/`）・本論文の `external.csv` で BS17・BM18 を引いている行があれば、その番号を README に一覧にする（既存の表は書き換えない）。

## 3. 規則

紙だけ。Lean の変更・ビルド・鍵の使用なし。証拠（PDF・抽出結果）は git の外、目録だけを `evidence/cited/<文献>/manifest.json` に。報告は `report-clmst-coverage.md` に節「CC-W3」を続け、現在地を更新。文献ごとにコミットし、三つ終わったら止まる。順は BS17 → BM18 → Rydh。
