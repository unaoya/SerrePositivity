# 文書の整理：段 0（紙）

作成：2026-11-17（調整役）。きっかけ：ユーザー「ドキュメントが増えてきたので整理したい」。この紙は方針と移動表の案で、まだ何も動かしていない。動いているレーンの報告は停止点まで動かさない。リンクは移動表で一括して直す。

## 現状（main 4e486b413 時点）

- `formalization-plans/` は 2,226 本・約 201 MB。うち `stage-ii/` が 169 MB（1,529 本）で、その 163.5 MB は検証の証拠（json 683・gz 613・py 148・log など）。大きいのは `bulk-b3prime/` 66 MB、`bulk-w1-b2/` 37 MB、`bulk-w1-b3/` 33 MB、`bulk-5inf3a/` 16 MB、`bulk-5inf0/` 4.3 MB。`archive/` 22 MB、`bhatt-scholze/` 7.7 MB（G12 の証拠 53 本を含む）。
- 追記で大きくなった報告：`bhatt-scholze/report-codex-w16.md` 23,559 行（⑤a）、`report-codex-m15.md` 18,560 行（⑤d）、`stage-ii/report-inf-supply-w2.md` 18,539 行（③-b の IS-W2）、`report-inf-supply-w1.md` 10,150 行（③-a）、`scheme-w1-2e-declarations.md` 3,931 行、`report-bulk-w1.md` 3,031 行。
- `.git` は 513 MB。すでに公開のリモートに push 済みなので、履歴を書き換えない限りリポジトリの大きさは減らない。

## (1) 正本の索引を README の先頭に

`formalization-plans/README.md` の先頭に「今の正本」を一つの表で置く（文書・役割・最終更新）。候補：
- 全体：`coordination.md`（レーン・ビルドの規則・暦）、`stage-ii/stage-ii-second-half.md`（段の表）、`coordinator-handover-2026-11.md`
- 方針：`stage-ii/p0-plan-draft.md`（P⁰ と文献に忠実に）、`stage-ii/p0-section-map.md`（地図・閉包の規則）、`stage-ii/infinity-consolidation-w1.md`（IC-W1）、`stage-ii/citation-attributes.md`
- 台帳：`refactor-ledger.md`、`refactor-plan.md`（論文の層）
- BS：`bhatt-scholze/design/design-status.md`（設計の決定 D 番号）
- K：`k-restart-draft.md`
- 各レーンの今の指示書と報告（レーンごとに一行）
研究資料の正本（対応表 `research/*-coverage/`、閉包 `research/p0-lurie/`）へのリンクも並べる。

## (2) stage-ii/ をレーンごとのサブディレクトリに

`stage-ii/scheme/`（⑥）、`inf-supply-a/`（③-a）、`inf-supply-b/`（③-b の IS-W2）、`consolidation/`（OE-W1・IC-W1）、`bulk/`（一括）、`p0/`（P⁰・地図）。共通の正本（`stage-ii-second-half.md`・`lane-goals-*.md`・`citation-attributes.md`）は `stage-ii/` の直下に残す。移動表は `move-table.csv`（列 src・dst・group・when・note、247 行。未分類 3 行は段 1 で判断）。

## (3) 報告の先頭に「現在地」、終わった段は archive へ

各報告の先頭に十数行の「現在地」：今の段、停止点、一覧の進み具合の一行、最新の検証済みコミット、残り、外枠。終わった段の節は `archive/reports/<報告名>-<段>.md` へ切り出し、元の報告には一行のリンクを残す。対象と時期：W16（⑤a、停止中）・M15（⑤d、停止中）・IS-W2（③-b の 3b-4、停止済み）はすぐ。③-a の `report-inf-supply-w1.md` は 5∞-1 の停止点の後。⑥ の報告は 2g-2 の停止点の後。今後の報告は「現在地」を保つことを各指示書に一行で入れる。

## (4) 検証の証拠のデータ

選択肢：(a) リポジトリの中の別ディレクトリ `evidence/`、(b) git の外（ローカルの保存場所）に置き、リポジトリには目録（パス・SHA-256・大きさ・作った手順）だけ、(c) Git LFS。
- **案**：既にあるものは (a) で `evidence/<レーン>/<段>/` へ `git mv`（履歴は変えない、`formalization-plans/` を文書だけにする）。**これからのものは (b)**：大きい生成物（gz・ログ・採取の json）は git の外（例 `~/serre-evidence/<レーン>/<段>/`、または本体の作業木の外の固定の場所）に置き、報告には目録だけをコミットする。検査を再現する py は、再利用するものは `scripts/<話題>/` へ、その段限りのものは証拠と一緒に。
- (c) LFS は採らない：公開リポジトリの帯域・容量の上限があり、既存の履歴は小さくならない。
- 決めること：git の外の保存場所（バックアップの有無）、目録の形（`evidence-manifest.json` の列）、各レーンの指示書への一行。

## (5) 段階 I の計画と infinity-lanes/ を archive へ

`archive/stage-i/` へ：`infinity-codex-g1.md`・`infinity-codex-g2*.md`・`infinity-foundation-plan.md`・`infinity-g2-progress.md`・`refactoring-infinity*.md`・`refactoring-verdier.md`・`handover-ct-to-infinity-2026-10-30.md`・`dg-cleanup-plan.md`（完了）・`cleanup-list-2026-11.md`、`infinity-lanes/`（26 本）、`kst-lanes/`（28 本。K の再開の前なので、`k-restart-draft.md` からの参照を移動表で直す）。`stage-ii-plan-draft.md` は stage-ii-second-half に置き換わっているが、決定の記録として参照されるので当面は残す（段 1 で判断）。

## (6) 手で保つ宣言の一覧を B5 の生成物に

手で書いた宣言の一覧（`scheme-w1-2e-declarations.md` 3,931 行、`scheme-w1-2f-declarations.md` 2,863 行、報告の末尾の「宣言と主張の一行ずつの一覧」など）は、ソースとずれやすい。B5（地図を属性から作る）の段で、モジュールごとの宣言と docstring の先頭の主張を Lean の環境かソースから生成するスクリプト（例 `scripts/docs/declaration_index.py`、出力は `research/declaration-index/`）を作り、手の一覧はそれに置き換える。B5 までは手の一覧は凍結（追記しない）し、新しい報告は宣言の一覧を書かずにコミットとモジュール名だけを書く。

## 進め方の案

- 段 1（すぐできる分）：(1) 索引、(5) 段階 I の archive、(2)・(3) のうち停止中のレーン（一括・P⁰・BS・IS-W2）の移動と分割、(4) の既存の証拠の `evidence/` への移動。文書だけの変更なので昼でよい（Lean のビルドは要らない）。リンクの書き換えは移動表から機械的に行い、`scripts/check_documentation.py` で切れたリンクがないことを確かめる。
- 段 2：動いているレーン（③-a・⑥・③-b の OE-W1）の報告を、それぞれの停止点で。
- 担当：手の空いたレーン（⑤a か ⑤d）か調整役。レーンの作業木の中の報告（main に入っていないもの）は動かさない。

## 追記（2026-11-17、ユーザー）：文書の相互の関係と将来の一本化

- **将来、人が読む解説は `exposition/` も含めてブループリント（`blueprint/`）に一本化する**（ユーザー 11-17）。ブループリントは対応表（`research/`）と Lean から生成し、手で書いた事実を持たない。短い日本語の主張と長い解説も、正本は `research/` の側（対応表の列、または解説の原稿）に置いて生成する形を目指す。
- それまでのつなぎ（案 a）：Artifact で公開している地図のページを、リポジトリの `research/<文献>-coverage/map/`（`template.html`・`data.json`）に置き、`scripts/docs/coverage_map.py` で作り直せるようにした（c1 の実施、2026-11-17）。P⁰ の地図は `research/p0-lurie/map/` に移した。
- 参照の向き：Lean は文献だけを引く。`research/` は文献と Lean を引く。`blueprint/` は `research/` と Lean から生成。`exposition/` は文献・Lean・ブループリントを引く（一本化まで）。`formalization-plans/` はどこを引いてもよいが、ほかの場所の中身は計画に頼らない。
