# 指示書 CC-W1：CLMST の対応表（紙）

作成：2026-11-17（調整役）。決定：ユーザー（11-17「CLMST をやりましょう」）。レーン：⑧ 引用文献（新設）。worktree `../SerrePositivity-cited`、枝 `research/cited-coverage`（main から）。**このチャットは worktree で開く**：最初に `pwd` が `…/SerrePositivity-cited` であることを確かめる。

## 0. 目的

本論文がいちばん多く引用している CLMST（Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, and an application to local fundamental groups*, arXiv 2209.04046v4）のブループリントを作るため、本論文の対応表（`research/paper-coverage/`）と同じ形の項目ごとの対応表を作る。本論文は CLMST 2.2.1・2.2.3・2.2.6(a)・4.0.1・4.0.4・4.0.10・4.0.14 を引用している（`research/paper-coverage/edges.csv`）。本体の形式化は主に `SerrePositivity/CLMST/`（18 本、約 6,500 行）にあり、`BhattScholze/`・`CommutativeAlgebra/` などからも使われている（docstring に CLMST の番号を書いたファイルは約 120 本）。

## 1. 対応表

置き場所：`research/clmst-coverage/`。形は `research/paper-coverage/` と同じ（README のファイルの説明を見る）。
- `toc.md`：採用版（arXiv 2209.04046v4、PDF は `../SerrePositivity/paper/refs/CLMST-2209.04046v4.pdf`。リポジトリの外にあるので読むだけ、写さない）、PDF の指紋、全見出し。
- `items.csv`：論文の**全**番号つき項目（Definition・Theorem・Lemma・Proposition・Corollary・Remark・Example・番号つきの式）。列は `research/paper-coverage/items.csv` と同じ 12 列（status・declarations・reason は空にして review から読む）。本論文が引く項目だけに限らない（文献に忠実に、項目単位で全部）。
- `review/ch<N>.csv`：節ごとに、状態（own・mathlib・both・partial・interface・none、意味は paper-coverage の README と同じ）、対応する宣言（`名前 @ パス:行`）、理由（仮定と結論の原典との差を日本語で）。特別な場合だけのもの（環や係数を狭めたもの）は partial にし、差を理由に書く。
- `edges.csv`：列 `number,depends_on,evidence_location,kind`。項目の主張と証明が引く、論文の中の項目（`internal`）と外の文献（`external`、`depends_on` は `research/bibliography.json` の略号か、なければ論文の文献番号）。
- `review/check/none-search.csv`：none の項目の検索語・範囲・採用しない理由。
- README に集計（状態ごとの数、辺の数）と主な確認結果。

## 2. 規則

- 紙だけ。Lean の変更・ビルド・`lake env lean` はしない（宣言の照合はソースを読む。kernel の確認ではないことを README に書く）。
- 既存の対応表（paper-coverage・bs-coverage など）は書き換えない。食い違いを見つけたら README に書いて報告する。
- 検証の証拠（採取の json など大きいもの）は git の外 `~/serre-evidence/cited/clmst/` に置き、目録だけを `scripts/docs/evidence_manifest.py` で `evidence/cited/clmst/manifest.json` に（`evidence/README.md`）。
- 報告は `formalization-plans/stage-ii/cited/report-clmst-coverage.md`。先頭に「現在地」（今の段・停止点・最新のコミット・残り）。宣言の一覧は報告に書かない（対応表にある）。
- 対応表をコミットしたら止まって報告する（停止点）。調整役が取り込んで、ブループリントの章を生成する。
