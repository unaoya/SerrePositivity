# R-B：安定・導来 ∞ 圏の整理

## 引き継ぎ

- 現在地：`refactor/r-b`、`../SerrePositivity-B`。基点 main `c6692be81` は checkpoint から計画文書だけが増えている。指定の .lake クローン完了。
  R24 は `aa2236b66` に保存。Stable・Derived・DGNerve 集約（11,358 jobs）、指定3監査、dg nerve 監査が成功。Derived は `-DmaxRecDepth=20000` を使用。
  Stable/KST 4 組を直接統合済みで、Stable・KST/SConstruction 集約ビルド成功（12,851 jobs）。両監査を実行中（session `74573`）。SemifreeLimits の本文はバイト一致、旧ファイルは削除。
- 残り（依存順）：Derived 準重複の直接統合、R3。
  R-A 取り込みの合図後に rebase・.lake 再クローンを行い、2-1〜2-3（Core/F1B への移動）。各項目の所要時間はビルド時間確認後に見積もる。
- 主要宣言：既存名を維持。`isTerminalVertex_semifree_zero`、`isInitialVertex_semifree_zero`、`semifreeFiberSquare`、
  `semifreeFiberSquare_isPullback`、`semifreeFiberSquare_inclusion` の所在は Derived/SemifreeLimits（名前空間 DGNerve を保持）。
- 依存と提供：Core/F1/F1B は R-A 取り込みまで読み取り専用。移動ツール未着につき、手変更を archive/refactor-r-b-manual-files.txt に記録。
- 未コミット：Derived データの差分表（Markdown・JSON）は次の Derived 項目でコミット予定。KST 統合一式は本コミットに保存する。
- 既知の問題：未追跡 DGKernelDerivedMapInvertible はユーザーの個別許可により main 作業ツリーから削除済み。
  DGKernelDerivedQuasiIsoMapInvertible と全非コメントトークンが一致することを削除直前に確認した。
- 次の一手：KST の項目別コミットを保存後、R-A のツール到着を確認し、一般宣言14組と Prop 共通化を適用する。適用後にデータ86宣言の本体不変性を検証。

## 方針

- 正本：refactoring-infinity.md §8 とユーザーの着手順指示。互換シムを残さず直接移動・置換する。
- 数学的内容・宣言の型・証明を維持し、新しい sorry・公理は追加しない。
- R24 は Derived/SemifreeLimits に移動し、DGNerve 集約から削除、Derived 集約に追加。
  DGNerve 名前空間の宣言名を変えず、dg nerve 監査には新所在を明示 import して既存チェックを保持。
- 集約ビルドは並行起動せず、単一コマンドで実行する。項目完了後は指定3監査を通し、承認待ちせず次へ進む。

## 後続作業と検証用スクリプト

- KST 4 本の削除と import/参照の直接置換はユーザーが追加許可済み。Stable 正本を保持する。
  11 宣言すべての型が Lean で定義的に等しい（`/tmp/r-b-kst-typecheck.lean`、成功ログ同名 `.log`）。
  `/tmp/r-b-kst-dedup.py` は適用済み。§5 にモジュール4組・宣言11個の対応表を記入。
- Derived の一般宣言14組はソースの型・証明トークンが名前置換後一致し、Lean で型の定義的同一性も確認済み。
  検証 `/tmp/r-b-derived-generic.py`、型チェック `/tmp/r-b-derived-typecheck.lean`（成功ログ同名 `.log`）。
  `python3 /tmp/r-b-derived-generic.py --apply` は canonical の宣言を DGNerve の新2ファイルへ直接移す予定。
- Prop の証明共有は型維持を条件にユーザー許可済み。新しい2補題の preview は Lean 単体検証成功。
  `/tmp/r-b-proof-cases.py --apply` は4定理の証明だけを共有化し、§5 に新補題の所在を記録する。
- データ構成は本体維持、D レーン再開後判断。指定の archive/refactor-near-duplicates-derived-2026-10-23.md に19組の差分表を保存済み。
- R-A からの move_module.py はまだ存在しない。rebase・再クローンはコーディネータの合図を待つ。

## 補足検証と許可待ち

- 14 宣言の共通移動先の preview は `/tmp/r-b-derived-combinatorics-preview.lean` と `/tmp/r-b-derived-vertex-preview.lean`。両方とも Lean 成功。
- データ本体の不変性は86宣言を `/tmp/r-b-data-golden.json` に保存済み。適用後に `python3 /tmp/r-b-data-invariant.py` を実行する。
- KST の統合は後続のユーザー指示に従い Stable・KST/SConstruction 集約、audit_infinity_stable・audit_kst_s_construction を検証する。
- R3 の VertexPrescribedExtension は KST/ZeroBoundaryExtension に依存する。その1本も Core へ直接移す追加許可を非同期で質問中。許可前には触らない。
- R3 の BoundaryOpposite は ColimitCoconeFamily への不要な import を除いても単体 Lean が通る（`/tmp/r-b-boundary-opposite-core-preview.lean`）。Core 移動の閉包を縮小できる。

## R3 の下準備（未適用）

- `/tmp/r-b-r3-core-preview.py` が7ファイルの一般論を束ねた preview を生成する。Core/Mathlib の直接 import 8本だけで Lean 成功（`/tmp/r-b-r3-core-preview.lean`、同 `.log`）。
- InitialOpposite の `IsZeroVertex.op` は零対象の定義を使うため Stable 側に残す。残り5宣言を Core 側へ分離すれば、Core→Stable を導入せず InitialExtension・ZeroBoundaryExtension・VertexPrescribedExtension を移動できる。
- LimitConeFamilies は元から Core だけに依存する。これも移動すれば LimitProjectionExistence の Core 移動に Stable 依存を持ち込まない。
- preview は移動可否の検証だけで、実ファイルはまだ変更していない。ZeroBoundaryExtension の追加所有許可と、Core へ移動する着手時期は要確認。

## 次の一手の補足

- KST の実行 session `74573` は終了（exit 0）。ビルド・両監査は成功済みで、再起動しない。
- 移動ツールが未着なら `/tmp/r-b-derived-generic.py --apply` → `/tmp/r-b-proof-cases.py --apply` → `/tmp/r-b-data-invariant.py`。適用後、Stable・Derived・DGNerve 集約と指定3監査を実行する。
- R23 の Core 移動には F2 の LimitConeExtension・SliceRestrictionEquivalence・SliceRestrictionEquivalenceLifting が必要。Core→F2 を残さないため、この3本の直接移動の追加許可を非同期で質問中（未許可では変更しない）。
- R23 preview：`/tmp/r-b-r23-preview.py` が Core だけの極限比較と、追加で F1B を使う cofinal 比較を生成する。検証ログは `/tmp/r-b-r23-{core,cofinal}-preview.log`。
