# R-B：安定・導来 ∞ 圏の整理

## 引き継ぎ

- 現在地：`refactor/r-b`、`../SerrePositivity-B`。基点 main `c6692be81` は checkpoint から計画文書だけが増えている。指定の .lake クローン完了。
- R24 は `aa2236b66`、Stable/KST 4組は `20f3cc257` に保存。集約ビルド・指定監査はすべて成功。
- Derived 共有化：一般宣言14組の直接共有化、旧モジュール8本削除、新規 Prop 補題2個・既存4定理の証明共有を実施。Stable・Derived・DGNerve 集約（11,353 jobs）と4監査成功。検証記録は archive/refactor-r-b-validation.md。
- データ86宣言の本体不変を確認。型依存データ19組は指定の差分表に保存し、D レーン再開後の判断へ保留。候補53組すべての統合完了とは扱わない。
- 残り：R3 と 2-1〜2-3。R-A 取り込みの合図後に rebase・.lake 再クローンを行い、Core/F1B への移動に着手。合図は未受領。
- Core/F1/F1B は取り込みまで読み取り専用。move_module.py 未着につき手変更は archive/refactor-r-b-manual-files.txt に記録。
- main の未追跡 DGKernelDerivedMapInvertible は個別許可により削除済み。既存 QuasiIso 版と全非コメントトークン一致を確認。
- 次の一手：R-A 取り込みの合図を待って rebase・.lake 再クローン。Derived 共有化は `e0ce9b2c8` に保存済み。session 12212 は exit 0、再実行しない。

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
  `python3 /tmp/r-b-derived-generic.py --apply` は適用済み。canonical 宣言を DGNerve の新2ファイルへ直接移動した。
- Prop の証明共有は型維持を条件にユーザー許可済み。新しい2補題の preview は Lean 単体検証成功。
  `/tmp/r-b-proof-cases.py --apply` は適用済み。4定理の証明だけ共有化し、§5 に新補題の所在を記録した。
- データ構成は本体維持、D レーン再開後判断。指定の archive/refactor-near-duplicates-derived-2026-10-23.md に19組の差分表を保存済み。
- R-A からの move_module.py はまだ存在しない。rebase・再クローンはコーディネータの合図を待つ。

## 補足検証と許可待ち

- 14 宣言の共通移動先の preview は `/tmp/r-b-derived-combinatorics-preview.lean` と `/tmp/r-b-derived-vertex-preview.lean`。両方とも Lean 成功。
- データ本体の不変性は86宣言を `/tmp/r-b-data-golden.json` に保存済み。適用後にも `python3 /tmp/r-b-data-invariant.py` が成功（86本体不変）。
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
- Derived の二つの移行スクリプトは適用済み。現在のデータ本体86個が不変で、残した14宣言の型・証明トークンも HEAD と一致し、書き換えた4定理のヘッダーも HEAD とバイト一致することを確認済み。
- R23 の F2 一般論3本（LimitConeExtension・SliceRestrictionEquivalence・SliceRestrictionEquivalenceLifting）の Core 直接移動・旧ファイル削除・機械的参照置換・集約更新は追加許可済み。実施は R-A 取り込み後の rebase 後。R-C/R19 後の所在から移す。
- R23 preview：`/tmp/r-b-r23-preview.py` が Core だけの極限比較と、追加で F1B を使う cofinal 比較を生成する。検証ログは `/tmp/r-b-r23-{core,cofinal}-preview.log`。

## R23 の承認済み移動先

- F2 の一般論3本と LimitDiagramIso は、Core だけの import で preview Lean が成功した。
- CofinalLimitExistence は型に F1B の IsLeftCofinal を含み、F1B の因子分解を使う。移動先を新規 F1B/CofinalLimitExistence とする調整はユーザー承認済み。型・証明を保持した preview も Lean 成功。

- R23 検証は Core・F2・Derived の集約と audit_infinity_core・audit_infinity_f2・audit_derived_infinity に加え audit_infinity_f1b（straightening を閉包に含まない）を実行。旧名→新名を §5 に記録する。

## R14 の下準備（未適用）

- PointConstantHomEquivalence と AdjunctionHomotopyCategory の本文を保った結合 preview は、Core・F1・F1B の import のみで Lean 成功。`/tmp/r-b-r14-f1b-preview.lean`、同 `.log`。実移動時は両方を新規 F1B ファイルへ置き、後者から前者を import する。

## R2・R22 の下準備（未適用）

- `/tmp/r-b-r2-initial-preview.py` が Cocone、ZeroHomotopy の一般論、InitialTransport の一般論をまとめた preview を生成。Core/Mathlib import のみ・autoImplicit false で Lean 成功（同名 `.lean`・`.log`）。ZeroHomotopy の IsZeroVertex.isZeroHo と hasZeroObject_ho、InitialTransport の IsZeroVertex.of_vertexIso は Stable に残す。
- UniverseLimits の閉包には HomotopyLimits/UniverseSSetMaps が必要。元の WeightedConeSectionEquivalence import は不要で、Core.Join と Mathlib の Types.Basic・Whiskering・SimplicialSet.Monoidal・NatIso だけで本文そのまま Lean 成功（`/tmp/r-b-universe-sset-maps-preview.lean`、同 `.log`、session 44668 exit 0）。
- UniverseSSetMaps → Core/UniverseSSetMaps の本文保持・直接移動はユーザー追加許可済み。WeightedConeSectionEquivalence import を外し、旧ファイル削除・importer 10本（HomotopyLimits 4・F2 4・Stable 1・Derived/Gluing 1）の機械的 import/参照置換・両集約更新を含む。実施は R-A・R-C 取り込み後の rebase 後。R19 後の所在を使う。検証は Core・HomotopyLimits・F2・Stable 集約と audit_infinity_core・audit_homotopy_limits。§5 に新所在を記録する。
- main は引き続き c6692be81。R-A 取り込みの合図は未受領。

## 宇宙比較・局所化の閉包検証（未適用）

- `/tmp/r-b-universe-closure-preview.py` は UniverseSSetMaps、Stable の UniverseJoinAugmentation・UniverseJoin・UniverseJoinNaturality・UniverseJoinSimplexShapes・UniverseBoundary・UniverseBoundaryHom・UniverseBoundaryFilling・UniverseJoinSimplexNaturality・UniverseConeHom・UniverseSlices と UniverseZeroObjects の先頭2補題を、本文を保持して結合する。Core/Mathlib import のみ・autoImplicit false で Lean 成功（同名 `.lean`・`.log`、session 96840 exit 0）。UniverseLimits 本体・反転依存はこの検証には含めない。
- R23 の局所化側は Derived の RightKanPrecompositionFaithful・LocalizationFunctorExtension・LocalizationRightKanCriterion・LocalizationPrecompositionCriterion・DeformationLocalization の5本で閉じる。本文を保持した `/tmp/r-b-localization-closure-preview.lean` は Core/F1B import のみ・autoImplicit false で Lean 成功（同 `.log`、session 90302 exit 0）。最初の2本も新規 F1B ファイルへ直接移せば F1B→Derived を残さない。全て元の所有範囲内。
- 上記は一時ファイルの検証のみ。移動実装は R-A 取り込みの合図・rebase 後。追加所有許可の未回答項目は ZeroBoundaryExtension の1本。UniverseSSetMaps は許可済みだが、R-A・R-C 取り込み後の rebase まで未実施。
