# R-B：安定・導来 ∞ 圏の整理

## 現在地と再開条件

- `refactor/r-b`、`../SerrePositivity-B`。ユーザーが取り込み方式を変更：**rebase はしない**。R-C の次に main 上で再適用する。`.lake` 再クローンを前提にした旧手順も取り消す。
- 今回は worktree 内の準備だけ完了。main のソース・index・ブランチは変更していない。
- 適用はコーディネータの **「main 空き」** の明示的な合図後。その間 main に書き込むのは R-B だけ。合図は未受領。
- main の確認基点は `571e451cc`。現在の checkout には R-A の未コミット変更があり、R-C の再適用は未完了。実適用直前に所在・ハッシュを再照合する。
- 再適用の正本：`archive/refactor-r-b-reapply-2026-10-23/manifest.json`。JSON 22本を作成。完了済み3項目・2-1〜2-4・検証・条件付き項目を分離した。

## 完了済みの実装と取り込み候補

1. `aa2236b66`：R24。SemifreeLimits を DGNerve から Derived へ本文そのまま移動。
2. `20f3cc257`：Stable/KST 4組。Stable 正本を保ち KST 重複4本を削除。11宣言の対応表あり。
3. `e0ce9b2c8`：Derived augmentation。一般宣言14組を共有、重複8本削除、Prop 補題2個で既存4定理の証明を共有。

- フルハッシュ・順序・全対象ファイルは bundle の `cherry-pick-commits.json`。文書だけのコミットは取り込まない。
- 3コミットの cherry-pick と対応する JSON 再適用は代替手段であり、二重に適用しない。競合時は現在の main/R-A/R-C の差分を保ち、R-B の差分だけを再適用する。ファイル全体の ours/theirs 置換は禁止。
- 集約ビルド・監査の成功記録は `archive/refactor-r-b-validation.md`。Derived 監査は `-DmaxRecDepth=20000` を使用。
- 未追跡 DGKernelDerivedMapInvertible はユーザー個別許可で main から削除済み。既存 QuasiIso 版と非コメントトークン一致を確認。
- 型依存データ19組は `archive/refactor-near-duplicates-derived-2026-10-23.md` に保存し、D レーン再開後の判断へ保留。データ86宣言の本体不変を確認済み。

## 次の移動（2-1〜2-4）の準備

- `10-r2-r22.*`：Cocone・宇宙比較・余極限図式比較を Core へ。宣言29個の部分抽出は exact body/hash 付き sidecar、モジュール移動と import 書き換えは move_module.py 用 JSON。Stable 固有の零対象宣言は残す。
- UniverseSSetMaps → Core は承認済み。WeightedConeSectionEquivalence import を外して Core/Mathlib の閉包にする。現在の直接 importer は集約込み18本（承認文の10本との差分を source snapshot に保存）。実適用前に R-C 後の所在を再確認する。
- F1 の sliceUnderRestrict_comp と instance sliceUnderRestrict_isIso → 新規 Core/SliceUnderRestriction は承認済み。現在の元ファイルは `F1/Joins/` 配下。型・本文・名前空間を保持し、元の2ファイルは固有内容と新 Core の public import を保持。実装コミット本文に **「F1 の 2 宣言を Core へ移した」** と明記する。
- `11-r14.*`：PointConstantHomEquivalence と AdjunctionHomotopyCategory を新規 F1B へ。
- `12-r23.*`：F2 の LimitConeExtension・SliceRestrictionEquivalence・SliceRestrictionEquivalenceLifting と Derived/LimitDiagramIso を Core、CofinalLimitExistence と局所化判定の閉包5本を F1B へ。現在 F2 3本は直下にあるが、R-C/R19 後は再探索する。
- `13-r3.*`：InitialExtension・LimitConeFamilies と KST の VertexPrescribedExtension・LimitProjectionExistence を Core へ。
- **未回答の追加所有許可：ZeroBoundaryExtension 1本**。`13-r3-zero-boundary.CONDITIONAL.*` は許可前に main へ適用しない。R3 の閉包のための条件付き計画として保存している。
- 全て互換シムなし。宣言の型・本文・名前空間を保持（明示した F2/KST の機械的名前空間移動を除く）。証明変更は承認済み4定理だけ。新規 sorry・公理なし。§5 に最終対応表を残す。

## 計画の検証結果と適用後のゲート

- 現在の main に対する読み取り専用 dry-run 7件が成功。main の対象ソース44本のハッシュを保存。
- 一時 Git fixture で13段階の順次 JSON 適用が成功（条件付き R3 は検証だけのシミュレーション）。新規 Core/F1B 43モジュールの静的閉包検査で禁止依存・不在モジュール0、DGNerve→Derived 直接 import 0。
- F1B の既存 Stable/HomotopyLimits 依存は新規追加と区別して記録。現行 audit_infinity_f1b と同じ straightening 禁止条件を維持し、既存 F1B 集約にない上位層診断の追加は0。
- `plan-validation.json` に結果と最終 JSON ハッシュ、`main-source-snapshot.json` に所在・ハッシュ・直接 importer 一覧。これは Lean の全体ビルドや監査の代用ではない。
- 適用後はユーザー指定の `scripts/refactor/verify.sh` を実行。各ビルド結果・**全監査の rc**・sorry 閉包をログで確認する（現行 verify.sh の最終終了コードだけでは全監査成功を保証しない）。
- 各項目の Stable・Derived 集約と audit_infinity_stable・audit_derived_infinity・audit_derived_gluing、追加許可に付随する Core/F1/F1B/F2/HomotopyLimits/KST の指定ゲートも維持する。
- Core の抽出29宣言は #check/#print axioms と R 移動 Core の再帰監査へ追加。移動前の監査範囲を落とさない。
- main の実適用 → verify.sh と全指定ゲート成功 → パス限定コミット → 報告。承認待ちで項目間を止めない。
