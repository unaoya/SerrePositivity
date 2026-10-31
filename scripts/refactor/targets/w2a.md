# IF-W0-3 W2a 束の計画草案（§10.14、静的 PASS・ビルド待機）

**W1＋W2a の静的 validator は PASS。束の実行・保存検査は未実施、§7-2 の受入条件は未達。** 対象草案と過去の3コミットはユーザー確認済み。§10.14 に従い分割先 import の自動追加を廃止した。DG-W1 取り込み通知と、R79・R75 を同じ束に含める案の確認を待つ。

## コミットと試験

| 区分 | commit | ファイル数 |
| --- | --- | --- |
| tools | 3a0134b595483a7d7d477530792d9f5f9e80b07f | 10 |
| tests | c6ed978e2bfc9d960495bb034da3b45c3a93c76b | 12 |
| records | 86fd55f38a9d005ef3061cd82993778995d6963c | 18 |

`python3 -B -m unittest discover -s scripts/refactor -p 'test_*.py'`：145 件 PASS、7.959 秒、exit 0。`zsh -n scripts/refactor/verify.sh`・`git diff --check`：exit 0。Lean を呼ぶ統合試験の main 関数は実行していない。mock の監査プロセスと一時 Git リポジトリの試験は含む。`decl_snapshot.lean` は既存の道具の変更として第1コミットに含めたが、数学 .lean の変更はない。

## W1 の計画上のルート import 修正

旧 JSON には既に削除された可換代数の import が 10 件残っていた。現 worktree のルート import と承認済みの ∞ 層入口 5 本の和集合へ更新した（786 → 785）。数学ソースは変更しない。W1 は move 62・split 3・reimport 3、計 68 件のまま。単独の静的検査は PASS、指標は不変。

| 削除された旧 import |
| --- |
| CommutativeAlgebra.Multiplicity |
| CommutativeAlgebra.ParameterAvoidance |
| CommutativeAlgebra.ParameterGeneratorPerturbation |
| CommutativeAlgebra.ParameterRadicalImage |
| CommutativeAlgebra.PrimeDimensionBounds |
| CommutativeAlgebra.RegularLocalCriterion |
| CommutativeAlgebra.RegularLocalization |
| CommutativeAlgebra.RegularParameters |
| CommutativeAlgebra.RegularPowerDivisibility |
| CommutativeAlgebra.RegularPrimeDimension |

| 現ルートに合わせて追加した import |
| --- |
| CommutativeAlgebra.RegularLocalRing.Basic |
| CommutativeAlgebra.RegularLocalRing.Criterion |
| CommutativeAlgebra.RegularLocalRing.Dimension |
| CommutativeAlgebra.RegularLocalRing.Localization |
| CommutativeAlgebra.RegularSequence |
| CommutativeAlgebra.SystemOfParameters.Avoidance |
| CommutativeAlgebra.SystemOfParameters.Basic |
| CommutativeAlgebra.SystemOfParameters.Finite |
| CommutativeAlgebra.SystemOfParameters.Generators |

この W1 修正と新しい w2a.json・w2a.md は、上記 3 コミット後の未コミット差分としてレビューに残す。

## 対象数

| action | 草案の件数 |
| --- | --- |
| move | 1197 |
| reimport | 2 |
| split | 9 |

| 候補 | 草案の項目数 |
| --- | --- |
| R56a | 1 |
| R64 | 357 |
| R64/R27 | 10 |
| R65 | 787 |
| R72(1)(2) | 9 |
| R72(3) | 44 |

w1.json と合わせて 1,276 項目。split 12 件＝W1 の 3 件＋W2a の 9 件であり、R72 の 12 モジュールがすべて split される意味ではない。R72 12 本のうち、Model の宣言を持たない 3 本は承認済み preflight と同じく空 split にせず保持し、純粋部分の移動を W2b 以降へ回す。

| R72 モジュール | moved | keep | 証拠・処置 |
| --- | --- | --- | --- |
| HA.Simplicial.Generators | 1 | 7 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.Simplicial.FixedBoundaryExtensions | 7 | 16 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.Simplicial.LargeParameterExtension | 3 | 4 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.Simplicial.UniverseLiftAnodyne | 1 | 4 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.Simplicial.BisimplicialCofibrancy | 2 | 3 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.Generated.Basic | 5 | 2 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.Generated.FunctorClosure | 0 | 3 | 分割不要：純粋部分の move は後の窓 |
| HA.Transfer.FullyFaithfulLifting | 0 | 1 | 分割不要：純粋部分の move は後の窓 |
| HA.HomotopyFunctionComplex.BoundaryOne | 0 | 5 | 分割不要：純粋部分の move は後の窓 |
| HA.HomotopyFunctionComplex.DiagonalFrame | 6 | 6 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.HomotopyFunctionComplex.QuillenStandardFrame | 2 | 4 | 個別 preflight PASS・復元済み。束の保存は未検証 |
| HA.HomotopyFunctionComplex.StandardCosimplicial | 2 | 6 | 静的 plan のみ。束で初検証 |

9 split の moved/keep は `.lake/verify/ifw0-3-addendum11/<basename>-plan.json` と一致する。8 本の imports は完了した試行の最終値、StandardCosimplicial は最小化していない静的 plan の両側 import を保持する。`downstream_imports` は実測済みの補充分だけとし、9 本とも空。これは未知の補充が不要という意味ではない。分割先の import は自動追加しない。束の失敗から確認した補充分だけを downstream_imports に記録する。古い plan.json の利用元への自動追加は適用せず、新しい prepare で分割元と分割先を生成する。

R72(3) の HL Quillen 42 本を ModelBridge へ移す。HL 集約から外し、ModelBridge 集約とルートを通して公開する reimport を 2 件置く。これらの入口変更も束のビルド待ち。

## §10.14 静的再検査（2026-10-31）

main `b3475df43` の §10.14 を `git show` で読んで実装。ブランチ `infra/if-w0-3`、HEAD `86fd55f38`、数学ソース基準 `831ad0de9`。main の merge・キャッシュ複製・Lean 実行・束の適用・verify・追加コミットは行っていない。

split は分割元・分割先の2ファイルだけを生成し、公開 import・simp・instance・本文の名前から利用元へ import を自動追加しない。validator は `downstream_imports` に書かれた分だけを合成する。中核の失敗からの補充は書き込み前に STOP し、利用元・エラー行の宣言・使用する移動宣言を報告する。実際の補充経路を持つ `prune_imports.py` もこの検査に接続した。

Python 試験は **150 件 PASS、7.730 秒、exit 0**。新規5件は中核への自動追加なし、失敗時の中核 STOP と復元、非中核の必要分だけの補充と復元、中核10層の停止、未使用宣言への補充なし。既存2件を新規則へ更新。Lean 呼び出しは mock に置換した試験だけで、実際の Lean ビルドはゼロ。

| 検査 | 秒 | 終了コード | status | 対象数 | 増加指標 |
| --- | --- | --- | --- | --- | --- |
| w1 | 55.085 | 0 | PASS | 68 | 0 |
| w1-w2a | 56.457 | 0 | PASS | 1276 | 0 |

実コマンドの全引数・時間は `.lake/verify/ifw0-3-addendum14/cli-results.json`。すべての split に保存済み `--snapshot MODULE=FILE`（W1 の3件＋R72 の9件）を渡し、snapshot 自動取得によるビルドを防いだ。

```text
python3 -B scripts/refactor/validate_targets.py scripts/refactor/targets/w1.json [scripts/refactor/targets/w2a.json] --snapshot MODULE=FILE ... --output .lake/verify/ifw0-3-addendum14/<w1|w1-w2a>.json
```

前回の増加指標 **2410 → 0**。`consumer_import_additions` は空。F2.Compact.WeakUniverse → ModelBridge.HA.UniverseLiftAnodyne と HomotopyLimits.KanTensorFrameAdjunction → ModelBridge.HA.QuillenStandardFrame の自動追加2辺が消えた。増加する根はなく、追加の鎖の報告対象はない。

### 層・閉包・入口（最新の静的模擬）

| 層の組 | 基準 | W1 後 | 前回 W1+W2a | 今回 W1+W2a |
| --- | --- | --- | --- | --- |
| F1 -> DGNerve | 1 | 0 | 0 | 0 |
| F1 -> Derived | 4 | 0 | 0 | 0 |
| F1 -> DoldKanComparison | 2 | 0 | 0 | 0 |
| F1 -> F2 | 28 | 17 | 17 | 17 |
| F1 -> SerrePositivity.HomotopicalAlgebra | 1 | 1 | 1 | 1 |
| F1 -> SerrePositivity.KST | 2 | 2 | 0 | 0 |
| F1 -> Stable | 23 | 23 | 23 | 23 |
| F1B -> Stable | 54 | 54 | 54 | 54 |
| F2 -> Derived | 7 | 3 | 3 | 3 |
| F2 -> ModelBridge | 0 | 0 | 1 | 0 |
| F2 -> SerrePositivity.HomotopicalAlgebra | 1 | 1 | 0 | 0 |
| F2 -> SerrePositivity.KST | 14 | 12 | 7 | 7 |
| HomotopyLimits -> DGNerve | 3 | 0 | 0 | 0 |
| HomotopyLimits -> Derived | 3 | 0 | 0 | 0 |
| HomotopyLimits -> DoldKanComparison | 2 | 0 | 0 | 0 |
| HomotopyLimits -> F2 | 84 | 82 | 82 | 82 |
| HomotopyLimits -> ModelBridge | 0 | 0 | 1 | 0 |
| HomotopyLimits -> SerrePositivity.HomotopicalAlgebra | 14 | 14 | 3 | 3 |
| HomotopyLimits -> SerrePositivity.KST | 26 | 26 | 16 | 16 |
| HomotopyLimits -> Stable | 50 | 50 | 50 | 50 |
| Stable -> Derived | 10 | 0 | 0 | 0 |
| Stable -> F2 | 42 | 40 | 40 | 40 |

| tier | 基準閉包 | W1 後 | 前回 W1+W2a | 今回 W1+W2a | 入口 基準/W1/前回/今回 |
| --- | --- | --- | --- | --- | --- |
| W1 | 2986 | 1 | 1 | 1 | 32 / 3 / 3 / 3 |
| W2a | 3257 | 257 | 195 | 178 | 90 / 59 / 32 / 30 |
| W2b | 3257 | 257 | 195 | 178 | 90 / 59 / 32 / 30 |

直接違反総数（基準/W1/前回/今回）：371 / 325 / 298 / 296。

**静的 ratchet の PASS は W2a の終了条件や束のビルド成功を意味しない。** 禁止閉包が残るため W2a の終了条件は未達。W1 の承認済み W2b 保留 FilteredSpaceBridgeInput も従前どおり。対象構成は変更せず、W1 68件＋W2a 1208件（move1197・split9・reimport2）のまま。R79・R75 は入れていない。

| 今回の W2a 入口元 | 入口先 |
| --- | --- |
| IC.F1.Universe.InnerAnodyne | HA.Generated.FunctorClosure |
| IC.F2.FilteredExchange.PiCriterion.BridgeComponents | IC.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput |
| IC.F2.FilteredExchange.PiCriterion.BridgePathTranspose | IC.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput |
| IC.F2.FilteredExchange.PiCriterion.BridgeStageKernel | IC.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput |
| IC.F2.FilteredExchange.PiCriterion.PairValueRepresentatives | KST.Spectra.FilteredLoopColimit |
| IC.F2.FilteredExchange.PiCriterion.PathFamilyHomotopy | KST.Spectra.UnbasedHomotopyIsomorphism |
| IC.F2.FilteredExchange.PiCriterion.PathTransport | KST.Spectra.UnbasedHomotopyIsomorphism |
| IC.F2.FilteredExchange.PiCriterion.PiPathSphereComparison | KST.Spectra.SphereMappingComponents |
| IC.F2.FilteredExchange.PiCriterion.PositiveValueRepresentatives | KST.Spectra.FilteredLoopColimit |
| IC.F2.FilteredExchange.PiCriterion.SphereClassPath | KST.Spectra.SphereSimplex |
| IC.F2.FilteredExchange.PiCriterion.SphereClassPath | KST.Spectra.UnbasedHomotopyIsomorphism |
| IC.HomotopyLimits.AdjunctionFrameHomBifunctor | HA.HomotopyFunctionComplex.AdjunctionHom |
| IC.HomotopyLimits.FibrationComponentTransport | KST.Spectra.FibrationIntervalLifting |
| IC.HomotopyLimits.IntervalHomBoundary | KST.Spectra.PointedInterval |
| IC.HomotopyLimits.KanTensorAdjunction | HA.HomotopyFunctionComplex.AdjunctionHom |
| IC.HomotopyLimits.KanTensorFrameAdjunction | HA.HomotopyFunctionComplex.QuillenStandardFrame |
| IC.HomotopyLimits.KanWhiteheadComparison | KST.Spectra.PointedKanWhitehead |
| IC.HomotopyLimits.LoopTowers | KST.Spectra.PostMappingFibration |
| IC.HomotopyLimits.MappingPathNaturality | KST.Spectra.MappingPathSpace |
| IC.HomotopyLimits.MappingPathTargetLifting | KST.Spectra.PointedKanWhitehead |
| IC.HomotopyLimits.PullbackFiberIso | KST.Spectra.PullbackKanSequence |
| IC.HomotopyLimits.RelativePointedHomLifting | KST.Spectra.PostMappingFibration |
| IC.HomotopyLimits.SpectrumBinaryProductSequence | KST.Spectra.KanSequence |
| IC.HomotopyLimits.SpectrumBinaryProductSequence | KST.Spectra.PointedGroupProduct |
| IC.HomotopyLimits.SpectrumMappingDiagram | KST.Spectra.CoherentNerve |
| IC.HomotopyLimits.SpectrumPullbackAdjoints | KST.Spectra.CofibrantOmegaSequence |
| IC.HomotopyLimits.SpectrumPullbackAdjoints | KST.Spectra.PostMappingFibration |
| IC.HomotopyLimits.SpectrumPullbackMonomorphisms | KST.Spectra.PullbackKanSequence |
| IC.HomotopyLimits.SpectrumTowerSequence | KST.Spectra.CofibrantOmegaSequence |
| IC.HomotopyLimits.TowerMatchingLifting | KST.Spectra.MonoRightHomotopyEquivalence |

## 三案比較（§10.13 の候補選定記録、今回は対象構成を変更しない）

W1 後の 59 入口辺を比較した。採用候補の pull-down 集合に 60 本超はない。R64 の宣言分割は指示書の対象外。上げる案の中核利用元一覧と完全な pull-down 集合は `three-options.json` に保存する。下表の採用は草案内の選択であり、束の承認ではない。

| 入口 | 下ろす本数／層 | 上げる本数／中核利用元 | 分割宣言数・適否 | 草案の処置 |
| --- | --- | --- | --- | --- |
| IC.F1.Limits.ContractibleKanTower → KST.Spectra.FibrationTowerLimitCone | 8 / Kan | 1 / 3165 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.F1.Limits.InverseSequenceQuasicategory → KST.Spectra.FibrationTowerLimitCone | 8 / Kan | 1 / 2229 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.F1.Universe.InnerAnodyne → HA.Generated.FunctorClosure | 2 / Kan | 1 / 1066 | 対象外／未採用 閉包に禁止依存が残る。宣言分割の保存証拠がないため採用せず保留 | 保留 |
| IC.F2.Compact.WeakUniverse → HA.Simplicial.UniverseLiftAnodyne | 21 / Kan | 1 / 682 | 1  | R72(1)(2) 分ける（指定された Model 宣言） |
| IC.F2.FilteredExchange.PiCriterion.BridgeComponents → IC.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput | 2209 / Kan | 1 / 4 | 対象外／未採用 閉包に禁止依存が残る。宣言分割の保存証拠がないため採用せず保留 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.BridgePathTranspose → IC.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput | 2209 / Kan | 1 / 7 | 対象外／未採用 閉包に禁止依存が残る。宣言分割の保存証拠がないため採用せず保留 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.BridgePathTranspose → KST.Spectra.HomotopyIso | 7 / Kan | 1 / 7 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.F2.FilteredExchange.PiCriterion.BridgeStageKernel → IC.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput | 2209 / Kan | 1 / 5 | 対象外／未採用 閉包に禁止依存が残る。宣言分割の保存証拠がないため採用せず保留 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.KanMapCriterion → KST.Spectra.HomotopyComponents | 8 / Kan | 1 / 7 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.F2.FilteredExchange.PiCriterion.PairValueRepresentatives → KST.Spectra.FilteredLoopColimit | 87 / Kan | 1 / 6 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.PairValueRepresentatives → KST.Spectra.HomotopyIso | 7 / Kan | 1 / 6 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.F2.FilteredExchange.PiCriterion.PathFamilyHomotopy → KST.Spectra.UnbasedHomotopyIsomorphism | 120 / Kan | 1 / 8 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.PathTransport → KST.Spectra.UnbasedHomotopyIsomorphism | 120 / Kan | 1 / 14 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.PiPathRelation → KST.Spectra.HomotopyIso | 7 / Kan | 1 / 13 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.F2.FilteredExchange.PiCriterion.PiPathRelation → KST.Spectra.HomotopySquares | 8 / Kan | 1 / 13 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.F2.FilteredExchange.PiCriterion.PiPathSphereComparison → KST.Spectra.SphereMappingComponents | 145 / Kan | 1 / 5 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.PositiveValueRepresentatives → KST.Spectra.FilteredLoopColimit | 87 / Kan | 1 / 2 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.SphereClassPath → KST.Spectra.SphereSimplex | 137 / Kan | 1 / 13 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.F2.FilteredExchange.PiCriterion.SphereClassPath → KST.Spectra.UnbasedHomotopyIsomorphism | 120 / Kan | 1 / 13 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.AdjunctionFrameHomBifunctor → HA.HomotopyFunctionComplex.AdjunctionHom | 2 / Kan | 1 / 5 | 対象外／未採用 閉包に禁止依存が残る。宣言分割の保存証拠がないため採用せず保留 | 保留 |
| IC.HomotopyLimits.ChosenQuillenFrameHom → HA.HomotopyFunctionComplex.ChosenMapComparison | 120 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.FibrationComponentTransport → KST.Spectra.FiberComponents | 15 / Kan | 1 / 2729 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.FibrationComponentTransport → KST.Spectra.FibrationIntervalLifting | 121 / Kan | 1 / 2729 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.FibrationTotalPositive → KST.Spectra.FibrationComparison | 21 / Kan | 1 / 28 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.FixedQuillenFrameComparison → HA.HomotopyFunctionComplex.FrameOverFunctor | 106 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.FixedQuillenFrameInvariance → HA.HomotopyFunctionComplex.HornTensor | 94 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.FixedQuillenFrameInvariance → HA.HomotopyFunctionComplex.RelativeBoundaryTensor | 19 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.GroupPointedFiveLemma → KST.Spectra.GroupFiveLemma | 1 / Kan | 1 / 29 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.IntervalHomBoundary → KST.Spectra.PointedInterval | 47 / Kan | 1 / 2591 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.KanPiProducts → KST.Spectra.HomotopyIsomorphism | 6 / Kan | 1 / 16 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.KanPiProducts → KST.Spectra.HomotopyProduct | 4 / Kan | 1 / 16 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.KanPiProducts → KST.Spectra.HomotopyZeroRelations | 6 / Kan | 1 / 16 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.KanTensorAdjunction → HA.HomotopyFunctionComplex.AdjunctionHom | 2 / Kan | 1 / 842 | 対象外／未採用 閉包に禁止依存が残る。宣言分割の保存証拠がないため採用せず保留 | 保留 |
| IC.HomotopyLimits.KanTensorFrameAdjunction → HA.HomotopyFunctionComplex.QuillenStandardFrame | 95 / Kan | 1 / 0 | 2  | R72(1)(2) 分ける（指定された Model 宣言） |
| IC.HomotopyLimits.KanWhiteheadComparison → KST.Spectra.PointedKanWhitehead | 136 / Kan | 1 / 2220 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.LoopTowers → KST.Spectra.PostMappingFibration | 74 / Kan | 1 / 4 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.MappingPathNaturality → KST.Spectra.MappingPathSpace | 123 / Kan | 1 / 12 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.MappingPathTargetLifting → KST.Spectra.PointedKanWhitehead | 136 / Kan | 1 / 7 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.PullbackFiberIso → KST.Spectra.PullbackKanSequence | 117 / Kan | 1 / 7 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.QuillenCfCollage → KST.SConstruction.EnrichedFunctorCollageNerve | 821 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.QuillenCfReplacementHom → HA.HomotopyFunctionComplex.ChosenMapComparison | 120 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.QuillenCfReplacementHom → HA.Quillen.CofibrantObjects | 2 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.QuillenCfReplacementHom → HA.Quillen.FibrantCriterion | 5 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.QuillenReplacedFrameHom → HA.HomotopyFunctionComplex.CosimplicialFrameFamily | 72 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.QuillenReplacedFrameHom → HA.HomotopyFunctionComplex.FramePreservation | 78 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.QuillenReplacedFrameHom → HA.HomotopyFunctionComplex.HornTensor | 94 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.QuillenReplacedFrameHom → HA.Quillen.FibrantCriterion | 5 / Kan | 42 / 0 | 対象外／未採用 指定の42本をまとめて移す。宣言分割は採用対象外 | R72(3) 上げる（指定42本をまとめる） |
| IC.HomotopyLimits.RelativePointedHomLifting → KST.Spectra.PostMappingFibration | 74 / Kan | 1 / 15 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |
| IC.HomotopyLimits.SpaceSequentialColimits → KST.Spectra.FilteredKanColimit | 6 / Kan | 1 / 1 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.SpectrumBinaryProductSequence → KST.Spectra.HomotopyIso | 7 / Kan | 1 / 15 | 11 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 下ろす |
| IC.HomotopyLimits.SpectrumBinaryProductSequence → KST.Spectra.KanSequence | 116 / Kan | 1 / 15 | 11 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 保留 |
| IC.HomotopyLimits.SpectrumBinaryProductSequence → KST.Spectra.PointedGroupProduct | 81 / Kan | 1 / 15 | 11 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 保留 |
| IC.HomotopyLimits.SpectrumMappingDiagram → KST.Spectra.CoherentNerve | 94 / Kan | 1 / 24 | 6 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 保留 |
| IC.HomotopyLimits.SpectrumPullbackAdjoints → KST.Spectra.CofibrantOmegaSequence | 123 / Kan | 1 / 4 | 3 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 保留 |
| IC.HomotopyLimits.SpectrumPullbackAdjoints → KST.Spectra.PostMappingFibration | 74 / Kan | 1 / 4 | 3 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 保留 |
| IC.HomotopyLimits.SpectrumPullbackMonomorphisms → KST.Spectra.PullbackKanSequence | 117 / Kan | 1 / 5 | 2 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 保留 |
| IC.HomotopyLimits.SpectrumTowerSequence → KST.Spectra.CofibrantOmegaSequence | 123 / Kan | 1 / 3 | 5 本文の型による分割候補。snapshot・分割試験は未実施。必要なSpectrum宣言に中核側の利用が残るため採用しない。 | 保留 |
| IC.HomotopyLimits.TowerMaps → KST.Spectra.FibrationTower | 7 / Kan | 1 / 14 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 下ろす |
| IC.HomotopyLimits.TowerMatchingLifting → KST.Spectra.MonoRightHomotopyEquivalence | 114 / Kan | 1 / 13 | 対象外／未採用 R64はモジュール閉包で判定し、宣言単位の分割は指示書の対象外 | 保留 |

## 束の実行手順（未実行・判断待ち）

§10.14 と最新指示に従う。現時点は静的検査までで停止。

1. DG-W1 が main に入った通知と束の構成の確認を待つ。R79・R75 の追加は未承認なので現 JSON に入れない。
2. 許可後に main を取り込み、対象・snapshot・改名の差分を確認する。他 worktree で lake build が走っていないことを確認し、指定の `rsync -a --delete ../SerrePositivity/.lake/build/ .lake/build/` を行う。DG 側の build lock・warm-up の道具を使う。
3. 新基準の snapshot と復元用ソースを保存し、W1 と W2a の split・move・reimport・既知の downstream_imports をすべて適用する。古い plan の自動 consumer 編集は持ち込まない。
4. 影響する下流の和集合を一回ビルドし、失敗した利用元だけへ必要分を補う。中核なら補充せず STOP して利用元・失敗宣言・使用する移動宣言を報告。非中核は層規則を確認し、補充と再検証を記録する。他 worktree と同時に全ビルドしない。
5. 全対象の after snapshot と保存比較、層・targets 検査を行う。入口 reimport はビルド・層検査で確認する。
6. `VERIFY_JOBS=3`、キャッシュなしで verify を一回行い PASS・gate:true を確認する。一時適用は復元する。

## 時間の見積もり

§10.14 の見積もりは、下流約20,000本を単独で1本1.0〜1.5秒、**6〜8時間**。前回の12.56時間は3セッション同時実行の実測による過大な見積もりだった。保存比較・verify・補充の時間は別。対象和集合は main 取り込みと束構成の承認後に再計測する。

## 候補の分類と保留

候補は R64 の指定ディレクトリと Sp/SC の主題群、その実際の import 先の補助、R56a の名前展開、R65 の3群から作った。必要な同群の依存が同時移動できる最大集合へ絞った。純粋部分だけの R72 元モジュール move は W2b 以降とし、今回の split と重ねない。本文の ModelCategory と Mathlib の SSet.modelCategoryQuillen 名前空間だけの使用は区別した。

- sp_starts: `BasedInterval`, `DependentProduct`, `EnrichedMapping`, `EnrichedOrderedCylinder`, `EnrichedParameter`, `EnrichedTransformation`, `EnrichedUnitTransformation`, `EnrichedWhiskered`, `Fiber`, `Fibration`, `FilteredHomotopy`, `FilteredKan`, `FunctionComplex`, `HomTensor`, `Homotopy`, `InternalHom`, `Loop`, `MappingPath`, `MonoRightHomotopy`, `NullHomotopy`, `Pointed`, `PostMapping`, `SelfPullback`, `SimplicialFunctionComplex`, `Skeletal`, `Skeleton`, `Smash`, `Spherical`, `Suspension`, `TensorMapping`, `Tower`, `Acyclic`, `Anodyne`, `Circle`, `Kan`, `Path`, `Pi`, `Whitehead`, `BasedLoop`, `BasedPathLoop`, `CoherentPath`, `CoherentSimplex`, `CoherentTetrahedron`, `CoherentTriangle`, `Horn`, `OrdinalSimplex`, `ReverseBoundaryEdge`, `SquareTriangle`, `ThreeEdgeTransport`, `FramedSquare`, `FramedTetrahedron`, `IntervalSquare`, `SquareBoundary`
- sp_exact: `AcyclicFiber`, `Commutativity`, `ContractibleTotalSequence`, `DiscreteInternalHom`, `DiscreteKanHomotopy`, `GroupExactTransfer`, `GroupFiveLemma`, `ParameterPoint`, `SequentialMittagLeffler`, `ZeroMapComponents`, `ConeEdgeIntervalCells`
- sc_starts: `CoherentArrow`, `CoherentPath`, `CoherentString`, `CompositionReplacement`, `CompositionTriple`, `ConcreteCube`, `Cube`, `Cubical`, `Cylinder`, `DoubleCylinder`, `ExInfinity`, `Filler`, `Fundamental`, `Homotopy`, `KanMapping`, `Necklace`, `Path`, `Pointed`, `SimplexClosedInterval`, `SimplexHABead`, `SimplexInterval`, `SimplexSubset`, `Smash`, `StrictSimplicial`, `Suspension`, `TriangleDiamond`, `SimplexInitial`, `SimplicialHomWhisker`, `VertexDiscreteFunctionSimplices`, `InternalUncurryEdgeEvaluation`, `SwapEvaluation`
- sc_exact: `CartesianFamilyEdgeTransport`, `CartesianInterchangeDiamond`, `CompositionDiamondImages`, `GroupoidBasedArrow`, `SwapNaturality`, `SpecifiedComparisonRestrictionComposition`

R56a 展開：`KST.LocalizingInvariants.CoreAnodyneLifting`, `KST.LocalizingInvariants.GeneralLocalization`, `KST.LocalizingInvariants.InverseAttachment`, `KST.LocalizingInvariants.InverseAttachmentLifting`, `KST.LocalizingInvariants.InverseAttachmentRestriction`, `KST.LocalizingInvariants.InverseAttachmentUniversal`, `KST.LocalizingInvariants.LocalizationFactorization`, `KST.LocalizingInvariants.LocalizationResolution`, `KST.LocalizingInvariants.LocalizationUniqueness`, `KST.LocalizingInvariants.ParametricDiagramGluing`, `KST.LocalizingInvariants.WalkingEquivalence`, `KST.LocalizingInvariants.WalkingEquivalenceRestriction`, `KST.LocalizingInvariants.WalkingEquivalenceUniversal`。

| 候補 | 保留数 |
| --- | --- |
| R27 | 4 |
| R56a | 12 |
| R64 | 1230 |
| R65 | 636 |

下記の 1,882 本は閉包・衝突・主題判定による不採用で JSON に含めない。以下の理由・本数・鎖は §10.13 時点の候補選定記録（自動追加を含む旧グラフ）を保存したもので、最新の閉包数は上の §10.14 表を参照する。今回は新規採用をしない。R27 の5個の上方移動案は中核の利用元を持ち、必要宣言の切り出しでもその入口が残るため保留。PullbackFiberIso の prune はまだ実行していないので reimport を入れていない。

| 候補 | モジュール | 理由・最初の禁止依存への鎖 |
| --- | --- | --- |
| R65 | EInfinity.FrameHom.AnodyneFamilyHomotopy |  禁止依存 60 本；EInfinity.FrameHom.AnodyneFamilyHomotopy → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.FrameHom.AnodyneWeakDetection |  禁止依存 59 本；EInfinity.FrameHom.AnodyneWeakDetection → HA.Simplicial.AnodyneHomotopyLocalization → HA.Simplicial.AnodyneIntervalEndpoints → IC.ModelBridge.HA.FixedBoundaryExtensions |
| R65 | EInfinity.FrameHom.ArrowSpanGrothendieck |  禁止依存 2 本；EInfinity.FrameHom.ArrowSpanGrothendieck → EInfinity.FrameHom.FrameElementSpans |
| R65 | EInfinity.FrameHom.AsSmallHammockHomFamily |  禁止依存 451 本；EInfinity.FrameHom.AsSmallHammockHomFamily → EInfinity.FrameHom.KanHomFamily |
| R65 | EInfinity.FrameHom.AsSmallHammockHomNormalization |  禁止依存 455 本；EInfinity.FrameHom.AsSmallHammockHomNormalization → EInfinity.FrameHom.AsSmallHammockHomFamily |
| R65 | EInfinity.FrameHom.BarInitialComparison |  禁止依存 120 本；EInfinity.FrameHom.BarInitialComparison → EInfinity.FrameHom.BarPointwiseInvariance |
| R65 | EInfinity.FrameHom.BarPointwiseInvariance |  禁止依存 119 本；EInfinity.FrameHom.BarPointwiseInvariance → EInfinity.FrameHom.BarRowsCoproduct |
| R65 | EInfinity.FrameHom.BarRowsCoproduct |  禁止依存 71 本；EInfinity.FrameHom.BarRowsCoproduct → HA.Simplicial.BarConstruction → HA.Simplicial.DiagonalAdjunction → HA.HomotopyFunctionComplex.DiagonalFrame |
| R65 | EInfinity.FrameHom.BarValueInclusion |  禁止依存 123 本；EInfinity.FrameHom.BarValueInclusion → EInfinity.FrameHom.BarInitialComparison |
| R65 | EInfinity.FrameHom.CofinalAnodyneImage |  禁止依存 15 本；EInfinity.FrameHom.CofinalAnodyneImage → HA.Simplicial.MonoRightLiftingContraction → HA.Simplicial.KanRelativeLifting → HA.Simplicial.KanHomotopyExtension → HA.Simplicial.HomotopyFaces → HA.Simplicial.LargeParameterHomotopy → IC.ModelBridge.HA.LargeParameterExtension |
| R65 | EInfinity.FrameHom.CommaNerveBarProjection |  禁止依存 124 本；EInfinity.FrameHom.CommaNerveBarProjection → EInfinity.FrameHom.CommaNerveContraction |
| R65 | EInfinity.FrameHom.CommaNerveContraction |  禁止依存 86 本；EInfinity.FrameHom.CommaNerveContraction → EInfinity.FrameHom.ThomasonSimplex |
| R65 | EInfinity.FrameHom.CommaPreLeftCofinality |  禁止依存 64 本；EInfinity.FrameHom.CommaPreLeftCofinality → EInfinity.FrameHom.CofinalAnodyneImage |
| R65 | EInfinity.FrameHom.ComonadResolutionFunctoriality |  禁止依存 1 本；EInfinity.FrameHom.ComonadResolutionFunctoriality → HA.HomotopyFunctionComplex.ComonadResolutionOperators |
| R65 | EInfinity.FrameHom.ComonadResolutionMap |  禁止依存 4 本；EInfinity.FrameHom.ComonadResolutionMap → EInfinity.FrameHom.ComonadResolutionFunctoriality |
| R65 | EInfinity.FrameHom.ConstantBarAugmentation |  禁止依存 121 本；EInfinity.FrameHom.ConstantBarAugmentation → EInfinity.FrameHom.BarPointwiseInvariance |
| R65 | EInfinity.FrameHom.ConstantBarRows |  禁止依存 86 本；EInfinity.FrameHom.ConstantBarRows → EInfinity.FrameHom.BarRowsCoproduct |
| R65 | EInfinity.FrameHom.CosimplicialHomCommaInvariance |  禁止依存 40 本；EInfinity.FrameHom.CosimplicialHomCommaInvariance → EInfinity.FrameHom.NerveEquivalenceImage |
| R65 | EInfinity.FrameHom.CosimplicialHomElements |  禁止依存 1 本；EInfinity.FrameHom.CosimplicialHomElements → HA.HomotopyFunctionComplex.ResolutionHom |
| R65 | EInfinity.FrameHom.EnrichedHomFunctor |  禁止依存 570 本；EInfinity.FrameHom.EnrichedHomFunctor → EInfinity.SimplicialLocalization.KanComparisonNerves |
| R65 | EInfinity.FrameHom.EnrichedHomRealization |  禁止依存 629 本；EInfinity.FrameHom.EnrichedHomRealization → EInfinity.FrameHom.EnrichedHomFunctor |
| R65 | EInfinity.FrameHom.EnrichedHomYoneda |  禁止依存 630 本；EInfinity.FrameHom.EnrichedHomYoneda → EInfinity.FrameHom.EnrichedHomRealization |
| R65 | EInfinity.FrameHom.FibrantFrameSpanComparison |  禁止依存 3 本；EInfinity.FrameHom.FibrantFrameSpanComparison → EInfinity.FrameHom.FibrantRightResolutionDiagram → EInfinity.FrameHom.CosimplicialHomCommaInvariance → EInfinity.FrameHom.OppositeElementsInvariance → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.FibrantFrameSpanNormalization |  禁止依存 3 本；EInfinity.FrameHom.FibrantFrameSpanNormalization → EInfinity.FrameHom.FibrantFrameSpanComparison → EInfinity.FrameHom.FibrantRightResolutionDiagram → EInfinity.FrameHom.CosimplicialHomCommaInvariance → EInfinity.FrameHom.OppositeElementsInvariance → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.FibrantRightResolutionDiagram |  禁止依存 3 本；EInfinity.FrameHom.FibrantRightResolutionDiagram → EInfinity.FrameHom.CosimplicialHomCommaInvariance → EInfinity.FrameHom.OppositeElementsInvariance → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.FibrantSourceReducedComparison |  禁止依存 3 本；EInfinity.FrameHom.FibrantSourceReducedComparison → EInfinity.FrameHom.FibrantFrameSpanNormalization → EInfinity.FrameHom.FibrantFrameSpanComparison → EInfinity.FrameHom.FibrantRightResolutionDiagram → EInfinity.FrameHom.CosimplicialHomCommaInvariance → EInfinity.FrameHom.OppositeElementsInvariance → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.FibrantSourceReducedFirst |  禁止依存 3 本；EInfinity.FrameHom.FibrantSourceReducedFirst → EInfinity.FrameHom.FibrantSourceReducedComparison → EInfinity.FrameHom.FibrantFrameSpanNormalization → EInfinity.FrameHom.FibrantFrameSpanComparison → EInfinity.FrameHom.FibrantRightResolutionDiagram → EInfinity.FrameHom.CosimplicialHomCommaInvariance → EInfinity.FrameHom.OppositeElementsInvariance → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.FixedRightGrothendieckInversion |  禁止依存 66 本；EInfinity.FrameHom.FixedRightGrothendieckInversion → EInfinity.FrameHom.CommaPreLeftCofinality |
| R65 | EInfinity.FrameHom.FrameArrowAugmentationLimits |  禁止依存 1617 本；EInfinity.FrameHom.FrameArrowAugmentationLimits → EInfinity.FrameHom.FrameArrowLimits |
| R65 | EInfinity.FrameHom.FrameArrowCofinality |  禁止依存 24 本；EInfinity.FrameHom.FrameArrowCofinality → IC.F1B.Cofinality.InitialTerminalWeakContractibility → IC.F1B.FunctorCategories.FunctorInitial → IC.F1B.FunctorCategories.FunctorRelativeInitial → IC.F1B.FunctorCategories.RelativeInitialExtension → IC.Stable.RelativeInitialBoundary |
| R65 | EInfinity.FrameHom.FrameArrowElements |  禁止依存 1 本；EInfinity.FrameHom.FrameArrowElements → HA.HomotopyFunctionComplex.ResolutionHom |
| R65 | EInfinity.FrameHom.FrameArrowLimits |  禁止依存 1615 本；EInfinity.FrameHom.FrameArrowLimits → EInfinity.FrameHom.FrameArrowCofinality |
| R65 | EInfinity.FrameHom.FrameArrowRightKan |  禁止依存 1620 本；EInfinity.FrameHom.FrameArrowRightKan → EInfinity.FrameHom.FrameArrowAugmentationLimits |
| R65 | EInfinity.FrameHom.FrameAugmentationLimitLegs |  禁止依存 1627 本；EInfinity.FrameHom.FrameAugmentationLimitLegs → EInfinity.FrameHom.FrameArrowAugmentationLimits |
| R65 | EInfinity.FrameHom.FrameElementSpans |  禁止依存 1 本；EInfinity.FrameHom.FrameElementSpans → HA.HomotopyFunctionComplex.ResolutionHom |
| R65 | EInfinity.FrameHom.FrameFunctorImage |  禁止依存 183 本；EInfinity.FrameHom.FrameFunctorImage → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.FrameHom.FrameIndexAugmentation |  禁止依存 33 本；EInfinity.FrameHom.FrameIndexAugmentation → EInfinity.FrameHom.SimplexTerminalEquivalence |
| R65 | EInfinity.FrameHom.FrameLeftRoof |  禁止依存 1 本；EInfinity.FrameHom.FrameLeftRoof → HA.HomotopyFunctionComplex.ResolutionHom |
| R65 | EInfinity.FrameHom.FrameLeftRoofPostcompose |  禁止依存 93 本；EInfinity.FrameHom.FrameLeftRoofPostcompose → EInfinity.FrameHom.FrameLeftRoof |
| R65 | EInfinity.FrameHom.FrameLeftRoofPrecompose |  禁止依存 95 本；EInfinity.FrameHom.FrameLeftRoofPrecompose → EInfinity.FrameHom.FrameLeftRoofPostcompose |
| R65 | EInfinity.FrameHom.FrameLiftComma |  禁止依存 124 本；EInfinity.FrameHom.FrameLiftComma → EInfinity.FrameHom.FrameLiftSimplices |
| R65 | EInfinity.FrameHom.FrameLiftContraction |  禁止依存 3 本；EInfinity.FrameHom.FrameLiftContraction → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.FrameLiftSimplices |  禁止依存 123 本；EInfinity.FrameHom.FrameLiftSimplices → EInfinity.FrameHom.FrameLiftContraction |
| R65 | EInfinity.FrameHom.FrameRightKan |  禁止依存 1629 本；EInfinity.FrameHom.FrameRightKan → EInfinity.FrameHom.FrameArrowAugmentationLimits |
| R65 | EInfinity.FrameHom.FrameRightKanCanonical |  禁止依存 1633 本；EInfinity.FrameHom.FrameRightKanCanonical → EInfinity.FrameHom.FrameRightKan |
| R65 | EInfinity.FrameHom.FrameRoofComparisonInvariance |  禁止依存 115 本；EInfinity.FrameHom.FrameRoofComparisonInvariance → EInfinity.FrameHom.FrameIndexAugmentation |
| R65 | EInfinity.FrameHom.FrameRoofCornerBaseProjection |  禁止依存 183 本；EInfinity.FrameHom.FrameRoofCornerBaseProjection → EInfinity.FrameHom.FrameRoofCornerProjectionLaws |
| R65 | EInfinity.FrameHom.FrameRoofCornerEvaluation |  禁止依存 81 本；EInfinity.FrameHom.FrameRoofCornerEvaluation → EInfinity.FrameHom.FrameRoofCornerNormalization |
| R65 | EInfinity.FrameHom.FrameRoofCornerEvaluationPrism |  禁止依存 88 本；EInfinity.FrameHom.FrameRoofCornerEvaluationPrism → EInfinity.FrameHom.FrameRoofCornerEvaluation |
| R65 | EInfinity.FrameHom.FrameRoofCornerEvaluationTriangle |  禁止依存 98 本；EInfinity.FrameHom.FrameRoofCornerEvaluationTriangle → EInfinity.FrameHom.FrameRoofCornerEvaluationPrism |
| R65 | EInfinity.FrameHom.FrameRoofCornerLeftBase |  禁止依存 100 本；EInfinity.FrameHom.FrameRoofCornerLeftBase → EInfinity.FrameHom.FrameRoofCornerEvaluationTriangle |
| R65 | EInfinity.FrameHom.FrameRoofCornerNormalization |  禁止依存 13 本；EInfinity.FrameHom.FrameRoofCornerNormalization → EInfinity.FrameHom.FrameRoofSliceFibration |
| R65 | EInfinity.FrameHom.FrameRoofCornerProjectionLaws |  禁止依存 182 本；EInfinity.FrameHom.FrameRoofCornerProjectionLaws → EInfinity.FrameHom.FrameRoofCornerEvaluationPrism |
| R65 | EInfinity.FrameHom.FrameRoofFiberPinched |  禁止依存 6 本；EInfinity.FrameHom.FrameRoofFiberPinched → EInfinity.FrameHom.FrameRoofTarget |
| R65 | EInfinity.FrameHom.FrameRoofFiberPinchedProjection |  禁止依存 7 本；EInfinity.FrameHom.FrameRoofFiberPinchedProjection → EInfinity.FrameHom.FrameRoofFiberPinched |
| R65 | EInfinity.FrameHom.FrameRoofQuillenSlice |  禁止依存 6 本；EInfinity.FrameHom.FrameRoofQuillenSlice → EInfinity.FrameHom.FrameRoofTarget |
| R65 | EInfinity.FrameHom.FrameRoofSliceFibration |  禁止依存 12 本；EInfinity.FrameHom.FrameRoofSliceFibration → EInfinity.FrameHom.FrameRoofQuillenSlice |
| R65 | EInfinity.FrameHom.FrameRoofSliceWeakContractibility |  禁止依存 167 本；EInfinity.FrameHom.FrameRoofSliceWeakContractibility → EInfinity.FrameHom.FrameRoofSliceFibration |
| R65 | EInfinity.FrameHom.FrameRoofSource |  禁止依存 2 本；EInfinity.FrameHom.FrameRoofSource → IC.Derived.RoofComparisonTransport |
| R65 | EInfinity.FrameHom.FrameRoofSourceProjection |  禁止依存 89 本；EInfinity.FrameHom.FrameRoofSourceProjection → EInfinity.FrameHom.FrameRoofCornerEvaluationPrism |
| R65 | EInfinity.FrameHom.FrameRoofTarget |  禁止依存 5 本；EInfinity.FrameHom.FrameRoofTarget → EInfinity.FrameHom.FrameRoofSource |
| R65 | EInfinity.FrameHom.FrameSpanNaturality |  禁止依存 2 本；EInfinity.FrameHom.FrameSpanNaturality → EInfinity.FrameHom.FrameElementSpans |
| R65 | EInfinity.FrameHom.FrameSpanTargetHomotopy |  禁止依存 91 本；EInfinity.FrameHom.FrameSpanTargetHomotopy → EInfinity.FrameHom.FrameSpanNaturality |
| R65 | EInfinity.FrameHom.FullyFaithfulNerveRetraction |  禁止依存 15 本；EInfinity.FrameHom.FullyFaithfulNerveRetraction → EInfinity.FrameHom.NerveEquivalenceImage |
| R65 | EInfinity.FrameHom.GrothendieckCommaComparison |  禁止依存 129 本；EInfinity.FrameHom.GrothendieckCommaComparison → EInfinity.FrameHom.CommaNerveBarProjection |
| R65 | EInfinity.FrameHom.GrothendieckCommaRetraction |  禁止依存 14 本；EInfinity.FrameHom.GrothendieckCommaRetraction → HA.Simplicial.AnodyneHomotopyLocalization → HA.Simplicial.AnodyneIntervalEndpoints → IC.ModelBridge.HA.FixedBoundaryExtensions |
| R65 | EInfinity.FrameHom.GrothendieckFiberInvariance |  禁止依存 178 本；EInfinity.FrameHom.GrothendieckFiberInvariance → EInfinity.FrameHom.ThomasonInversion |
| R65 | EInfinity.FrameHom.HeterogeneousSmallComma |  禁止依存 21 本；EInfinity.FrameHom.HeterogeneousSmallComma → EInfinity.FrameHom.NerveAsSmall |
| R65 | EInfinity.FrameHom.HomInfinityEquivalenceTransport |  禁止依存 302 本；EInfinity.FrameHom.HomInfinityEquivalenceTransport → IC.F2.Compact.HomCovariantComparison |
| R65 | EInfinity.FrameHom.HomInfinityLocalizationTransport |  禁止依存 319 本；EInfinity.FrameHom.HomInfinityLocalizationTransport → EInfinity.FrameHom.HomInfinityEquivalenceTransport |
| R65 | EInfinity.FrameHom.KanHomFamily |  禁止依存 120 本；EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap |
| R65 | EInfinity.FrameHom.LocalizationComparison |  禁止依存 26 本；EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.FrameHom.MixedFrame |  禁止依存 72 本；EInfinity.FrameHom.MixedFrame → HA.HomotopyFunctionComplex.ResolutionHom |
| R65 | EInfinity.FrameHom.MixedFrameSource |  禁止依存 127 本；EInfinity.FrameHom.MixedFrameSource → EInfinity.FrameHom.MixedFrameDiagrams |
| R65 | EInfinity.FrameHom.MixedNerveCoconePoint |  禁止依存 28 本；EInfinity.FrameHom.MixedNerveCoconePoint → EInfinity.FrameHom.MixedNerveCoconePrism |
| R65 | EInfinity.FrameHom.MixedNerveCoconePrism |  禁止依存 27 本；EInfinity.FrameHom.MixedNerveCoconePrism → EInfinity.FrameHom.MixedNerveNatTrans |
| R65 | EInfinity.FrameHom.MixedNerveConstant |  禁止依存 27 本；EInfinity.FrameHom.MixedNerveConstant → EInfinity.FrameHom.MixedNerveNatTrans |
| R65 | EInfinity.FrameHom.MixedNerveConstantHom |  禁止依存 28 本；EInfinity.FrameHom.MixedNerveConstantHom → EInfinity.FrameHom.MixedNerveNatTransFunctor |
| R65 | EInfinity.FrameHom.MixedNerveHomLiftIso |  禁止依存 1623 本；EInfinity.FrameHom.MixedNerveHomLiftIso → EInfinity.FrameHom.MixedNerveHomRecovery |
| R65 | EInfinity.FrameHom.MixedNerveHomRecovery |  禁止依存 1622 本；EInfinity.FrameHom.MixedNerveHomRecovery → EInfinity.FrameHom.MixedNerveNatTransFunctor |
| R65 | EInfinity.FrameHom.MixedNerveNatTrans |  禁止依存 26 本；EInfinity.FrameHom.MixedNerveNatTrans → IC.Derived.HomotopyComponentPrecomp |
| R65 | EInfinity.FrameHom.MixedNerveNatTransFunctor |  禁止依存 27 本；EInfinity.FrameHom.MixedNerveNatTransFunctor → EInfinity.FrameHom.MixedNerveNatTrans |
| R65 | EInfinity.FrameHom.NerveAsSmall |  禁止依存 19 本；EInfinity.FrameHom.NerveAsSmall → IC.ModelBridge.HA.UniverseLiftAnodyne |
| R65 | EInfinity.FrameHom.NerveColumnComponentArrow |  禁止依存 1619 本；EInfinity.FrameHom.NerveColumnComponentArrow → EInfinity.FrameHom.NerveColumnRoofNaturality |
| R65 | EInfinity.FrameHom.NerveColumnNaturalityComponent |  禁止依存 2171 本；EInfinity.FrameHom.NerveColumnNaturalityComponent → EInfinity.FrameHom.NerveColumnComponentArrow |
| R65 | EInfinity.FrameHom.NerveColumnRoofNaturality |  禁止依存 1618 本；EInfinity.FrameHom.NerveColumnRoofNaturality → EInfinity.FrameHom.FrameArrowAugmentationLimits |
| R65 | EInfinity.FrameHom.NerveEquivalenceImage |  禁止依存 14 本；EInfinity.FrameHom.NerveEquivalenceImage → HA.Simplicial.AnodyneHomotopyLocalization → HA.Simplicial.AnodyneIntervalEndpoints → IC.ModelBridge.HA.FixedBoundaryExtensions |
| R65 | EInfinity.FrameHom.NerveOverRightPrism |  禁止依存 42 本；EInfinity.FrameHom.NerveOverRightPrism → EInfinity.FrameHom.FrameRoofFiberPinchedProjection |
| R65 | EInfinity.FrameHom.NerveQuillenA |  禁止依存 61 本；EInfinity.FrameHom.NerveQuillenA → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.FrameHom.NerveTerminalImage |  禁止依存 14 本；EInfinity.FrameHom.NerveTerminalImage → HA.Simplicial.AnodyneHomotopyLocalization → HA.Simplicial.AnodyneIntervalEndpoints → IC.ModelBridge.HA.FixedBoundaryExtensions |
| R65 | EInfinity.FrameHom.OppositeElementsInvariance |  禁止依存 28 本；EInfinity.FrameHom.OppositeElementsInvariance → EInfinity.FrameHom.SimplexTerminalEquivalence |
| R65 | EInfinity.FrameHom.OverTerminalEvaluation |  禁止依存 14 本；EInfinity.FrameHom.OverTerminalEvaluation → EInfinity.FrameHom.TerminalFiberBaseHomotopy |
| R65 | EInfinity.FrameHom.PinchedFamilyWeakDetection |  禁止依存 61 本；EInfinity.FrameHom.PinchedFamilyWeakDetection → EInfinity.Hammock.WeakAnodyneLocalization |
| R65 | EInfinity.FrameHom.PointSliceCornerFibration |  禁止依存 4 本；EInfinity.FrameHom.PointSliceCornerFibration → IC.Derived.SliceRoofCorner |
| R65 | EInfinity.FrameHom.ProductSimplexElementProjectionWeak |  禁止依存 81 本；EInfinity.FrameHom.ProductSimplexElementProjectionWeak → EInfinity.FrameHom.FrameIndexAugmentation |
| R65 | EInfinity.FrameHom.ProductSimplexUniverseProjectionWeak |  禁止依存 81 本；EInfinity.FrameHom.ProductSimplexUniverseProjectionWeak → EInfinity.FrameHom.FrameIndexAugmentation |
| R65 | EInfinity.FrameHom.RealizationHomNaturality |  禁止依存 99 本；EInfinity.FrameHom.RealizationHomNaturality → HA.HomotopyFunctionComplex.Realization |
| R65 | EInfinity.FrameHom.ResolutionAsphericity |  禁止依存 3 本；EInfinity.FrameHom.ResolutionAsphericity → EInfinity.FrameHom.ResolutionCommaContraction → EInfinity.FrameHom.FrameLiftComma → EInfinity.FrameHom.FrameLiftSimplices → EInfinity.FrameHom.FrameLiftContraction → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.ResolutionCofinality |  禁止依存 3 本；EInfinity.FrameHom.ResolutionCofinality → EInfinity.FrameHom.ResolutionAsphericity → EInfinity.FrameHom.ResolutionCommaContraction → EInfinity.FrameHom.FrameLiftComma → EInfinity.FrameHom.FrameLiftSimplices → EInfinity.FrameHom.FrameLiftContraction → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.ResolutionCommaContraction |  禁止依存 3 本；EInfinity.FrameHom.ResolutionCommaContraction → EInfinity.FrameHom.FrameLiftComma → EInfinity.FrameHom.FrameLiftSimplices → EInfinity.FrameHom.FrameLiftContraction → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.ResolutionFixedRightComparison |  禁止依存 3 本；EInfinity.FrameHom.ResolutionFixedRightComparison → EInfinity.FrameHom.ResolutionCofinality → EInfinity.FrameHom.ResolutionAsphericity → EInfinity.FrameHom.ResolutionCommaContraction → EInfinity.FrameHom.FrameLiftComma → EInfinity.FrameHom.FrameLiftSimplices → EInfinity.FrameHom.FrameLiftContraction → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.RightFrameHammockCoherent |  禁止依存 62 本；EInfinity.FrameHom.RightFrameHammockCoherent → EInfinity.FrameHom.RightFrameHammockKanSpan → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.RightFrameHammockComponent |  禁止依存 62 本；EInfinity.FrameHom.RightFrameHammockComponent → EInfinity.FrameHom.RightFrameHammockCoherent → EInfinity.FrameHom.RightFrameHammockKanSpan → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.RightFrameHammockComponentImage |  禁止依存 62 本；EInfinity.FrameHom.RightFrameHammockComponentImage → EInfinity.FrameHom.RightFrameHammockComponent → EInfinity.FrameHom.RightFrameHammockCoherent → EInfinity.FrameHom.RightFrameHammockKanSpan → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.RightFrameHammockFamily |  禁止依存 3 本；EInfinity.FrameHom.RightFrameHammockFamily → EInfinity.FrameHom.SourceRoofFamily → EInfinity.FrameHom.FrameIndexAugmentation → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.RightFrameHammockKanSpan |  禁止依存 62 本；EInfinity.FrameHom.RightFrameHammockKanSpan → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.RightFrameHammockUnitComparison |  禁止依存 62 本；EInfinity.FrameHom.RightFrameHammockUnitComparison → EInfinity.FrameHom.RightFrameHammockUnitPoints → EInfinity.FrameHom.RightFrameHammockComponentImage → EInfinity.FrameHom.RightFrameHammockComponent → EInfinity.FrameHom.RightFrameHammockCoherent → EInfinity.FrameHom.RightFrameHammockKanSpan → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.RightFrameHammockUnitPoints |  禁止依存 62 本；EInfinity.FrameHom.RightFrameHammockUnitPoints → EInfinity.FrameHom.RightFrameHammockComponentImage → EInfinity.FrameHom.RightFrameHammockComponent → EInfinity.FrameHom.RightFrameHammockCoherent → EInfinity.FrameHom.RightFrameHammockKanSpan → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.RightFrameHomInfinity |  禁止依存 121 本；EInfinity.FrameHom.RightFrameHomInfinity → EInfinity.FrameHom.RightFrameTerminalHomReduction → EInfinity.FrameHom.HomInfinityLocalizationTransport → EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.FrameHom.RightFrameHomInfinityNormalization |  禁止依存 2462 本；EInfinity.FrameHom.RightFrameHomInfinityNormalization → EInfinity.FrameHom.AsSmallHammockHomNormalization → EInfinity.FrameHom.AsSmallHammockHomFamily → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.RightFrameRoofComparison |  禁止依存 3 本；EInfinity.FrameHom.RightFrameRoofComparison → EInfinity.FrameHom.ResolutionFixedRightComparison → EInfinity.FrameHom.ResolutionCofinality → EInfinity.FrameHom.ResolutionAsphericity → EInfinity.FrameHom.ResolutionCommaContraction → EInfinity.FrameHom.FrameLiftComma → EInfinity.FrameHom.FrameLiftSimplices → EInfinity.FrameHom.FrameLiftContraction → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.RightFrameSpecifiedLocalization |  禁止依存 74 本；EInfinity.FrameHom.RightFrameSpecifiedLocalization → EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.FrameHom.RightFrameSpecifiedUnit |  禁止依存 74 本；EInfinity.FrameHom.RightFrameSpecifiedUnit → EInfinity.FrameHom.RightFrameSpecifiedLocalization → EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.FrameHom.RightFrameTerminalHomReduction |  禁止依存 121 本；EInfinity.FrameHom.RightFrameTerminalHomReduction → EInfinity.FrameHom.HomInfinityLocalizationTransport → EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.FrameHom.RightFrameTerminalRealization |  禁止依存 99 本；EInfinity.FrameHom.RightFrameTerminalRealization → EInfinity.FrameHom.AsSmallHammockHomFamily → EInfinity.FrameHom.KanHomFamily → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.FrameHom.SimplexTerminalEquivalence |  禁止依存 27 本；EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard |
| R65 | EInfinity.FrameHom.SimplexTerminalFunctor |  禁止依存 3 本；EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.SimplexTerminalStandard |  禁止依存 19 本；EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.NerveTerminalImage |
| R65 | EInfinity.FrameHom.SmallCommaContraction |  禁止依存 21 本；EInfinity.FrameHom.SmallCommaContraction → EInfinity.FrameHom.NerveAsSmall |
| R65 | EInfinity.FrameHom.SmallCommaGrothendieck |  禁止依存 21 本；EInfinity.FrameHom.SmallCommaGrothendieck → EInfinity.FrameHom.NerveAsSmall |
| R65 | EInfinity.FrameHom.SmallCosimplicialHomElements |  禁止依存 2 本；EInfinity.FrameHom.SmallCosimplicialHomElements → EInfinity.FrameHom.CosimplicialHomElements |
| R65 | EInfinity.FrameHom.SmallNerveInvariance |  禁止依存 20 本；EInfinity.FrameHom.SmallNerveInvariance → EInfinity.FrameHom.NerveAsSmall |
| R65 | EInfinity.FrameHom.SourceRoofFamily |  禁止依存 3 本；EInfinity.FrameHom.SourceRoofFamily → EInfinity.FrameHom.FrameIndexAugmentation → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.SourceRoofUnitNormalization |  禁止依存 3 本；EInfinity.FrameHom.SourceRoofUnitNormalization → EInfinity.FrameHom.SourceRoofFamily → EInfinity.FrameHom.FrameIndexAugmentation → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.FrameHom.TerminalFiberBaseHomotopy |  禁止依存 13 本；EInfinity.FrameHom.TerminalFiberBaseHomotopy → IC.Derived.RoofTerminalEvaluation |
| R65 | EInfinity.FrameHom.TerminalFiberEvaluationWeak |  禁止依存 65 本；EInfinity.FrameHom.TerminalFiberEvaluationWeak → EInfinity.Hammock.WeakAnodyneLocalization |
| R65 | EInfinity.FrameHom.ThomasonInversion |  禁止依存 1131 本；EInfinity.FrameHom.ThomasonInversion → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.FrameHom.ThomasonNaturality |  禁止依存 191 本；EInfinity.FrameHom.ThomasonNaturality → EInfinity.FrameHom.ThomasonNerveMap |
| R65 | EInfinity.FrameHom.ThomasonNerveMap |  禁止依存 190 本；EInfinity.FrameHom.ThomasonNerveMap → EInfinity.FrameHom.BarValueInclusion |
| R65 | EInfinity.FrameHom.ThomasonSimplex |  禁止依存 75 本；EInfinity.FrameHom.ThomasonSimplex → HA.Simplicial.BarConstruction |
| R65 | EInfinity.FrameHom.UnitComparisonTransport |  禁止依存 65 本；EInfinity.FrameHom.UnitComparisonTransport → EInfinity.ComplexLimits.PinchedTransportFamily |
| R65 | EInfinity.FrameHom.UnitComparisonWeakDetection |  禁止依存 62 本；EInfinity.FrameHom.UnitComparisonWeakDetection → EInfinity.FrameHom.PinchedFamilyWeakDetection |
| R65 | EInfinity.Hammock.AllMarkedCompositionPoints |  禁止依存 45 本；EInfinity.Hammock.AllMarkedCompositionPoints → EInfinity.Hammock.AllMarkedNative |
| R65 | EInfinity.Hammock.AllMarkedDetector |  禁止依存 44 本；EInfinity.Hammock.AllMarkedDetector → EInfinity.Hammock.AllMarkedNative |
| R65 | EInfinity.Hammock.AllMarkedEmbedding |  禁止依存 45 本；EInfinity.Hammock.AllMarkedEmbedding → EInfinity.Hammock.AllMarkedDetector |
| R65 | EInfinity.Hammock.AllMarkedEmptyIso |  禁止依存 52 本；EInfinity.Hammock.AllMarkedEmptyIso → EInfinity.Hammock.UnmarkedEmptySpace |
| R65 | EInfinity.Hammock.AllMarkedEndpointTransport |  禁止依存 44 本；EInfinity.Hammock.AllMarkedEndpointTransport → EInfinity.Hammock.AllMarkedNative |
| R65 | EInfinity.Hammock.AllMarkedEnrichedInclusion |  禁止依存 48 本；EInfinity.Hammock.AllMarkedEnrichedInclusion → EInfinity.Hammock.AllMarkedUnitPoints |
| R65 | EInfinity.Hammock.AllMarkedEvaluationWeak |  禁止依存 142 本；EInfinity.Hammock.AllMarkedEvaluationWeak → EInfinity.Hammock.AllMarkedNative |
| R65 | EInfinity.Hammock.AllMarkedImage |  禁止依存 50 本；EInfinity.Hammock.AllMarkedImage → EInfinity.Hammock.AllMarkedEmbedding |
| R65 | EInfinity.Hammock.AllMarkedLocalizationValueComparison |  禁止依存 177 本；EInfinity.Hammock.AllMarkedLocalizationValueComparison → EInfinity.Hammock.LocalizationValue |
| R65 | EInfinity.Hammock.AllMarkedNative |  禁止依存 43 本；EInfinity.Hammock.AllMarkedNative → EInfinity.Hammock.RelativeColimitMap |
| R65 | EInfinity.Hammock.AllMarkedUnitPoints |  禁止依存 47 本；EInfinity.Hammock.AllMarkedUnitPoints → EInfinity.Hammock.AllMarkedCompositionPoints |
| R65 | EInfinity.Hammock.AnodyneComponents |  禁止依存 15 本；EInfinity.Hammock.AnodyneComponents → HA.Simplicial.PiZeroLocalization → HA.Simplicial.KanTestDetection → HA.Simplicial.AnodyneKanReplacement → IC.ModelBridge.HA.Generators |
| R65 | EInfinity.Hammock.AsSmallArrow |  禁止依存 61 本；EInfinity.Hammock.AsSmallArrow → EInfinity.Hammock.AsSmallComparison |
| R65 | EInfinity.Hammock.AsSmallComparison |  禁止依存 60 本；EInfinity.Hammock.AsSmallComparison → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.Hammock.AsSmallComposition |  禁止依存 62 本；EInfinity.Hammock.AsSmallComposition → EInfinity.Hammock.AsSmallArrow |
| R65 | EInfinity.Hammock.AsSmallKanArrow |  禁止依存 123 本；EInfinity.Hammock.AsSmallKanArrow → EInfinity.Hammock.AsSmallArrow |
| R65 | EInfinity.Hammock.CoefficientProductDiagonal |  禁止依存 61 本；EInfinity.Hammock.CoefficientProductDiagonal → EInfinity.Hammock.WeakTensor |
| R65 | EInfinity.Hammock.CoherentComponents |  禁止依存 15 本；EInfinity.Hammock.CoherentComponents → HA.Simplicial.PiZeroLocalization → HA.Simplicial.KanTestDetection → HA.Simplicial.AnodyneKanReplacement → IC.ModelBridge.HA.Generators |
| R65 | EInfinity.Hammock.ContractibleMaps |  禁止依存 61 本；EInfinity.Hammock.ContractibleMaps → EInfinity.Hammock.WeakTwoOfSix |
| R65 | EInfinity.Hammock.ContravariantThomasonArrows |  禁止依存 81 本；EInfinity.Hammock.ContravariantThomasonArrows → EInfinity.FrameHom.ThomasonSimplex |
| R65 | EInfinity.Hammock.ContravariantThomasonSimplex |  禁止依存 85 本；EInfinity.Hammock.ContravariantThomasonSimplex → EInfinity.Hammock.ContravariantGrothendieckComponents |
| R65 | EInfinity.Hammock.DoubleSimplicialColumnWeak |  禁止依存 168 本；EInfinity.Hammock.DoubleSimplicialColumnWeak → EInfinity.FrameHom.BarPointwiseInvariance |
| R65 | EInfinity.Hammock.DoubleSimplicialWeak |  禁止依存 160 本；EInfinity.Hammock.DoubleSimplicialWeak → EInfinity.Hammock.WeakAnodyneLocalization |
| R65 | EInfinity.Hammock.EmptyWordDiagonalWeak |  禁止依存 166 本；EInfinity.Hammock.EmptyWordDiagonalWeak → EInfinity.Hammock.DoubleSimplicialWeak |
| R65 | EInfinity.Hammock.EraseEmbedding |  禁止依存 26 本；EInfinity.Hammock.EraseEmbedding → EInfinity.Hammock.RawEmbeddingComparison |
| R65 | EInfinity.Hammock.EraseEraseConfluence |  禁止依存 27 本；EInfinity.Hammock.EraseEraseConfluence → EInfinity.Hammock.EraseSimplexIdentityColumn |
| R65 | EInfinity.Hammock.EraseSimplex |  禁止依存 23 本；EInfinity.Hammock.EraseSimplex → EInfinity.Hammock.ProperDiagram |
| R65 | EInfinity.Hammock.EraseSimplexIdentityColumn |  禁止依存 24 本；EInfinity.Hammock.EraseSimplexIdentityColumn → EInfinity.Hammock.EraseSimplex |
| R65 | EInfinity.Hammock.EraseSimplexNaturality |  禁止依存 24 本；EInfinity.Hammock.EraseSimplexNaturality → EInfinity.Hammock.EraseSimplex |
| R65 | EInfinity.Hammock.ExInfinityEnrichedFunctor |  禁止依存 77 本；EInfinity.Hammock.ExInfinityEnrichedFunctor → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.Hammock.ExInfinityEnrichedUnit |  禁止依存 78 本；EInfinity.Hammock.ExInfinityEnrichedUnit → EInfinity.Hammock.ExInfinityEnrichedFunctor |
| R65 | EInfinity.Hammock.ExInfinityPointActions |  禁止依存 141 本；EInfinity.Hammock.ExInfinityPointActions → EInfinity.Hammock.ExInfinityEnrichedUnit |
| R65 | EInfinity.Hammock.ExInfinityWeakMap |  禁止依存 1011 本；EInfinity.Hammock.ExInfinityWeakMap → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.Hammock.FiniteGridRootHull |  禁止依存 102 本；EInfinity.Hammock.FiniteGridRootHull → EInfinity.Hammock.QuiverTreeFiniteContractible |
| R65 | EInfinity.Hammock.FiniteProduct |  禁止依存 61 本；EInfinity.Hammock.FiniteProduct → EInfinity.Hammock.WeakTensor |
| R65 | EInfinity.Hammock.FirstColumnBackwardBackwardCatIso |  禁止依存 64 本；EInfinity.Hammock.FirstColumnBackwardBackwardCatIso → EInfinity.Hammock.NerveWeakTransport |
| R65 | EInfinity.Hammock.FirstColumnBackwardBackwardDiagonalAugmentation |  禁止依存 210 本；EInfinity.Hammock.FirstColumnBackwardBackwardDiagonalAugmentation → EInfinity.Hammock.FirstColumnBackwardBackwardDiagramIso |
| R65 | EInfinity.Hammock.FirstColumnBackwardBackwardDiagramIso |  禁止依存 208 本；EInfinity.Hammock.FirstColumnBackwardBackwardDiagramIso → EInfinity.Hammock.FirstColumnBackwardBackwardCatIso |
| R65 | EInfinity.Hammock.FirstColumnBackwardBackwardRelativeFunctor |  禁止依存 204 本；EInfinity.Hammock.FirstColumnBackwardBackwardRelativeFunctor → EInfinity.Hammock.FirstColumnBackwardBackwardRelativeObject |
| R65 | EInfinity.Hammock.FirstColumnBackwardBackwardRelativeObject |  禁止依存 203 本；EInfinity.Hammock.FirstColumnBackwardBackwardRelativeObject → EInfinity.Hammock.TwoSidedDiagramTotal |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardAugmentation |  禁止依存 68 本；EInfinity.Hammock.FirstColumnBackwardForwardAugmentation → EInfinity.Hammock.FirstColumnBackwardForwardDiagram |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardCatIso |  禁止依存 64 本；EInfinity.Hammock.FirstColumnBackwardForwardCatIso → EInfinity.Hammock.NerveWeakTransport |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardData |  禁止依存 65 本；EInfinity.Hammock.FirstColumnBackwardForwardData → EInfinity.Hammock.FirstColumnBackwardForwardCatIso |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardDataCoherence |  禁止依存 66 本；EInfinity.Hammock.FirstColumnBackwardForwardDataCoherence → EInfinity.Hammock.FirstColumnBackwardForwardData |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardDiagonalAugmentation |  禁止依存 214 本；EInfinity.Hammock.FirstColumnBackwardForwardDiagonalAugmentation → EInfinity.Hammock.FirstColumnBackwardForwardAugmentation |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardDiagram |  禁止依存 67 本；EInfinity.Hammock.FirstColumnBackwardForwardDiagram → EInfinity.Hammock.FirstColumnBackwardForwardDataCoherence |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardDiagramIso |  禁止依存 211 本；EInfinity.Hammock.FirstColumnBackwardForwardDiagramIso → EInfinity.Hammock.FirstColumnBackwardForwardCatIso |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardRelativeFunctor |  禁止依存 206 本；EInfinity.Hammock.FirstColumnBackwardForwardRelativeFunctor → EInfinity.Hammock.FirstColumnBackwardForwardRelativeObject |
| R65 | EInfinity.Hammock.FirstColumnBackwardForwardRelativeObject |  禁止依存 205 本；EInfinity.Hammock.FirstColumnBackwardForwardRelativeObject → EInfinity.Hammock.FirstColumnBackwardForwardData |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardAugmentation |  禁止依存 68 本；EInfinity.Hammock.FirstColumnForwardBackwardAugmentation → EInfinity.Hammock.FirstColumnForwardBackwardDiagram |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardCatIso |  禁止依存 64 本；EInfinity.Hammock.FirstColumnForwardBackwardCatIso → EInfinity.Hammock.NerveWeakTransport |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardData |  禁止依存 65 本；EInfinity.Hammock.FirstColumnForwardBackwardData → EInfinity.Hammock.FirstColumnForwardBackwardCatIso |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardDataCoherence |  禁止依存 66 本；EInfinity.Hammock.FirstColumnForwardBackwardDataCoherence → EInfinity.Hammock.FirstColumnForwardBackwardData |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardDiagonalAugmentation |  禁止依存 214 本；EInfinity.Hammock.FirstColumnForwardBackwardDiagonalAugmentation → EInfinity.Hammock.FirstColumnForwardBackwardAugmentation |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardDiagram |  禁止依存 67 本；EInfinity.Hammock.FirstColumnForwardBackwardDiagram → EInfinity.Hammock.FirstColumnForwardBackwardDataCoherence |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardDiagramIso |  禁止依存 211 本；EInfinity.Hammock.FirstColumnForwardBackwardDiagramIso → EInfinity.Hammock.FirstColumnForwardBackwardCatIso |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardRelativeFunctor |  禁止依存 206 本；EInfinity.Hammock.FirstColumnForwardBackwardRelativeFunctor → EInfinity.Hammock.FirstColumnForwardBackwardRelativeObject |
| R65 | EInfinity.Hammock.FirstColumnForwardBackwardRelativeObject |  禁止依存 205 本；EInfinity.Hammock.FirstColumnForwardBackwardRelativeObject → EInfinity.Hammock.FirstColumnForwardBackwardData |
| R65 | EInfinity.Hammock.FirstColumnForwardForwardDiagonalAugmentation |  禁止依存 209 本；EInfinity.Hammock.FirstColumnForwardForwardDiagonalAugmentation → EInfinity.Hammock.FirstColumnForwardForwardDiagramIso |
| R65 | EInfinity.Hammock.FirstColumnForwardForwardDiagramIso |  禁止依存 207 本；EInfinity.Hammock.FirstColumnForwardForwardDiagramIso → EInfinity.Hammock.FirstColumnForwardForwardRelativeFunctor |
| R65 | EInfinity.Hammock.FirstColumnForwardForwardRelativeFunctor |  禁止依存 204 本；EInfinity.Hammock.FirstColumnForwardForwardRelativeFunctor → EInfinity.Hammock.FirstColumnForwardForwardRelativeObject |
| R65 | EInfinity.Hammock.FirstColumnForwardForwardRelativeObject |  禁止依存 203 本；EInfinity.Hammock.FirstColumnForwardForwardRelativeObject → EInfinity.Hammock.TwoSidedDiagramTotal |
| R65 | EInfinity.Hammock.FirstColumnForwardForwardWeak |  禁止依存 64 本；EInfinity.Hammock.FirstColumnForwardForwardWeak → EInfinity.Hammock.NerveWeakTransport |
| R65 | EInfinity.Hammock.FixedObjectComposition |  禁止依存 45 本；EInfinity.Hammock.FixedObjectComposition → EInfinity.Hammock.RelativeFixedColimitMap |
| R65 | EInfinity.Hammock.FixedObjectEvaluationComposition |  禁止依存 48 本；EInfinity.Hammock.FixedObjectEvaluationComposition → EInfinity.Hammock.FixedObjectLocalizationEvaluation |
| R65 | EInfinity.Hammock.FixedObjectHomTransportIso |  禁止依存 47 本；EInfinity.Hammock.FixedObjectHomTransportIso → EInfinity.Hammock.FixedObjectLocalizationEvaluation |
| R65 | EInfinity.Hammock.FixedObjectLocalizationEvaluation |  禁止依存 46 本；EInfinity.Hammock.FixedObjectLocalizationEvaluation → EInfinity.Hammock.FixedObjectLocalizationValue |
| R65 | EInfinity.Hammock.FixedObjectLocalizationValue |  禁止依存 45 本；EInfinity.Hammock.FixedObjectLocalizationValue → EInfinity.Hammock.LocalizationValueNaturality |
| R65 | EInfinity.Hammock.ForwardPathZigzagLaws |  禁止依存 5 本；EInfinity.Hammock.ForwardPathZigzagLaws → EInfinity.Hammock.ForwardPathZigzag |
| R65 | EInfinity.Hammock.FreeFirstColumnBackwardHomWeak |  禁止依存 284 本；EInfinity.Hammock.FreeFirstColumnBackwardHomWeak → EInfinity.Hammock.FreeFirstColumnBackwardObjects |
| R65 | EInfinity.Hammock.FreeFirstColumnBackwardLeftWeak |  禁止依存 286 本；EInfinity.Hammock.FreeFirstColumnBackwardLeftWeak → EInfinity.Hammock.FreeFirstColumnBackwardHomWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnBackwardObjects |  禁止依存 248 本；EInfinity.Hammock.FreeFirstColumnBackwardObjects → EInfinity.Hammock.FirstColumnBackwardBackwardDiagonalAugmentation |
| R65 | EInfinity.Hammock.FreeFirstColumnBackwardRightDiagram |  禁止依存 286 本；EInfinity.Hammock.FreeFirstColumnBackwardRightDiagram → EInfinity.Hammock.FreeFirstColumnBackwardHomWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnBackwardRightGraph |  禁止依存 287 本；EInfinity.Hammock.FreeFirstColumnBackwardRightGraph → EInfinity.Hammock.FreeFirstColumnBackwardRightDiagram |
| R65 | EInfinity.Hammock.FreeFirstColumnBackwardRightWeak |  禁止依存 291 本；EInfinity.Hammock.FreeFirstColumnBackwardRightWeak → EInfinity.Hammock.FreeFirstColumnBackwardRightGraph |
| R65 | EInfinity.Hammock.FreeFirstColumnBackwardStep |  禁止依存 297 本；EInfinity.Hammock.FreeFirstColumnBackwardStep → EInfinity.Hammock.FreeFirstColumnBackwardLeftWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnForwardStep |  禁止依存 289 本；EInfinity.Hammock.FreeFirstColumnForwardStep → EInfinity.Hammock.FreeFirstColumnLeftWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnHomWeak |  禁止依存 277 本；EInfinity.Hammock.FreeFirstColumnHomWeak → EInfinity.Hammock.FreeFirstColumnObjects |
| R65 | EInfinity.Hammock.FreeFirstColumnLeftDiagram |  禁止依存 279 本；EInfinity.Hammock.FreeFirstColumnLeftDiagram → EInfinity.Hammock.FreeFirstColumnHomWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnLeftGraph |  禁止依存 280 本；EInfinity.Hammock.FreeFirstColumnLeftGraph → EInfinity.Hammock.FreeFirstColumnLeftDiagram |
| R65 | EInfinity.Hammock.FreeFirstColumnLeftWeak |  禁止依存 283 本；EInfinity.Hammock.FreeFirstColumnLeftWeak → EInfinity.Hammock.FreeFirstColumnLeftGraph |
| R65 | EInfinity.Hammock.FreeFirstColumnMixedHomWeak |  禁止依存 288 本；EInfinity.Hammock.FreeFirstColumnMixedHomWeak → EInfinity.Hammock.FreeFirstColumnHomWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnMixedObjects |  禁止依存 252 本；EInfinity.Hammock.FreeFirstColumnMixedObjects → EInfinity.Hammock.FirstColumnForwardBackwardDiagonalAugmentation |
| R65 | EInfinity.Hammock.FreeFirstColumnMixedPointWeak |  禁止依存 290 本；EInfinity.Hammock.FreeFirstColumnMixedPointWeak → EInfinity.Hammock.FreeFirstColumnMixedHomWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnMixedRightIso |  禁止依存 306 本；EInfinity.Hammock.FreeFirstColumnMixedRightIso → EInfinity.Hammock.CoefficientProductDiagonal |
| R65 | EInfinity.Hammock.FreeFirstColumnMixedRightWeak |  禁止依存 307 本；EInfinity.Hammock.FreeFirstColumnMixedRightWeak → EInfinity.Hammock.FreeFirstColumnMixedRightIso |
| R65 | EInfinity.Hammock.FreeFirstColumnMixedStep |  禁止依存 312 本；EInfinity.Hammock.FreeFirstColumnMixedStep → EInfinity.Hammock.FreeFirstColumnMixedPointWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnObjects |  禁止依存 242 本；EInfinity.Hammock.FreeFirstColumnObjects → EInfinity.Hammock.FirstColumnForwardForwardDiagonalAugmentation |
| R65 | EInfinity.Hammock.FreeFirstColumnReverseHomWeak |  禁止依存 288 本；EInfinity.Hammock.FreeFirstColumnReverseHomWeak → EInfinity.Hammock.FreeFirstColumnHomWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnReverseLeftIso |  禁止依存 305 本；EInfinity.Hammock.FreeFirstColumnReverseLeftIso → EInfinity.Hammock.CoefficientProductDiagonal |
| R65 | EInfinity.Hammock.FreeFirstColumnReverseLeftWeak |  禁止依存 306 本；EInfinity.Hammock.FreeFirstColumnReverseLeftWeak → EInfinity.Hammock.FreeFirstColumnReverseLeftIso |
| R65 | EInfinity.Hammock.FreeFirstColumnReverseObjects |  禁止依存 252 本；EInfinity.Hammock.FreeFirstColumnReverseObjects → EInfinity.Hammock.FirstColumnBackwardForwardDiagonalAugmentation |
| R65 | EInfinity.Hammock.FreeFirstColumnReversePointWeak |  禁止依存 290 本；EInfinity.Hammock.FreeFirstColumnReversePointWeak → EInfinity.Hammock.FreeFirstColumnReverseHomWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnReverseStep |  禁止依存 311 本；EInfinity.Hammock.FreeFirstColumnReverseStep → EInfinity.Hammock.FreeFirstColumnReverseLeftWeak |
| R65 | EInfinity.Hammock.FreeFirstColumnRightWeak |  禁止依存 279 本；EInfinity.Hammock.FreeFirstColumnRightWeak → EInfinity.Hammock.FreeFirstColumnHomWeak |
| R65 | EInfinity.Hammock.FreeHammockEnrichedFold |  禁止依存 114 本；EInfinity.Hammock.FreeHammockEnrichedFold → EInfinity.Hammock.MarkedSpineEnrichedFoldUnique |
| R65 | EInfinity.Hammock.FreeHammockEnrichedFoldUnique |  禁止依存 115 本；EInfinity.Hammock.FreeHammockEnrichedFoldUnique → EInfinity.Hammock.FreeHammockEnrichedFold |
| R65 | EInfinity.Hammock.FreeHammockEnrichedFreeProduct |  禁止依存 129 本；EInfinity.Hammock.FreeHammockEnrichedFreeProduct → EInfinity.Hammock.FreeHammockEnrichedRestrictionParts |
| R65 | EInfinity.Hammock.FreeHammockEnrichedFreeProductFac |  禁止依存 130 本；EInfinity.Hammock.FreeHammockEnrichedFreeProductFac → EInfinity.Hammock.FreeHammockEnrichedFreeProduct |
| R65 | EInfinity.Hammock.FreeHammockEnrichedInclusions |  禁止依存 127 本；EInfinity.Hammock.FreeHammockEnrichedInclusions → EInfinity.Hammock.FreeHammockEnrichedPartsEquiv |
| R65 | EInfinity.Hammock.FreeHammockEnrichedParts |  禁止依存 123 本；EInfinity.Hammock.FreeHammockEnrichedParts → EInfinity.Hammock.UnmarkedFreeEnrichedFunctor |
| R65 | EInfinity.Hammock.FreeHammockEnrichedPartsData |  禁止依存 124 本；EInfinity.Hammock.FreeHammockEnrichedPartsData → EInfinity.Hammock.FreeHammockEnrichedParts |
| R65 | EInfinity.Hammock.FreeHammockEnrichedPartsEquiv |  禁止依存 126 本；EInfinity.Hammock.FreeHammockEnrichedPartsEquiv → EInfinity.Hammock.FreeHammockEnrichedPartsRecovery |
| R65 | EInfinity.Hammock.FreeHammockEnrichedPartsRecovery |  禁止依存 125 本；EInfinity.Hammock.FreeHammockEnrichedPartsRecovery → EInfinity.Hammock.FreeHammockEnrichedPartsData |
| R65 | EInfinity.Hammock.FreeHammockEnrichedRestriction |  禁止依存 117 本；EInfinity.Hammock.FreeHammockEnrichedRestriction → EInfinity.Hammock.AllMarkedEnrichedInclusion |
| R65 | EInfinity.Hammock.FreeHammockEnrichedRestrictionParts |  禁止依存 128 本；EInfinity.Hammock.FreeHammockEnrichedRestrictionParts → EInfinity.Hammock.FreeHammockEnrichedInclusions |
| R65 | EInfinity.Hammock.FreeHammockEnrichedUniversal |  禁止依存 121 本；EInfinity.Hammock.FreeHammockEnrichedUniversal → EInfinity.Hammock.FreeHammockEnrichedRestriction |
| R65 | EInfinity.Hammock.FreeHammockLocalizationWeak |  禁止依存 217 本；EInfinity.Hammock.FreeHammockLocalizationWeak → EInfinity.Hammock.MarkedSpineLocalizationEvaluation |
| R65 | EInfinity.Hammock.FreeQuiverCoverContractible |  禁止依存 127 本；EInfinity.Hammock.FreeQuiverCoverContractible → EInfinity.Hammock.FreeQuiverCoverFiniteContractible |
| R65 | EInfinity.Hammock.FreeQuiverCoverFiniteContractible |  禁止依存 104 本；EInfinity.Hammock.FreeQuiverCoverFiniteContractible → EInfinity.Hammock.QuiverTreeFiniteWeakMaps |
| R65 | EInfinity.Hammock.FreeQuiverCoverGraphValue |  禁止依存 43 本；EInfinity.Hammock.FreeQuiverCoverGraphValue → EInfinity.Hammock.HammockValue |
| R65 | EInfinity.Hammock.FreeQuiverCoverHammockFiber |  禁止依存 46 本；EInfinity.Hammock.FreeQuiverCoverHammockFiber → EInfinity.Hammock.FreeQuiverCoverValueFiberDiagram |
| R65 | EInfinity.Hammock.FreeQuiverCoverNerveFiber |  禁止依存 44 本；EInfinity.Hammock.FreeQuiverCoverNerveFiber → EInfinity.Hammock.FreeQuiverCoverGraphValue |
| R65 | EInfinity.Hammock.FreeQuiverCoverValueFiberDiagram |  禁止依存 45 本；EInfinity.Hammock.FreeQuiverCoverValueFiberDiagram → EInfinity.Hammock.FreeQuiverCoverNerveFiber |
| R65 | EInfinity.Hammock.FreeQuiverEvaluationWeak |  禁止依存 138 本；EInfinity.Hammock.FreeQuiverEvaluationWeak → EInfinity.Hammock.FreeQuiverCoverContractible |
| R65 | EInfinity.Hammock.GraphEmbedding |  禁止依存 21 本；EInfinity.Hammock.GraphEmbedding → EInfinity.Hammock.NerveEmbedding |
| R65 | EInfinity.Hammock.GrothendieckPointwiseWeak |  禁止依存 179 本；EInfinity.Hammock.GrothendieckPointwiseWeak → EInfinity.FrameHom.ThomasonInversion |
| R65 | EInfinity.Hammock.HammockValue |  禁止依存 42 本；EInfinity.Hammock.HammockValue → EInfinity.Hammock.ReducedColimit |
| R65 | EInfinity.Hammock.HammockValueComposition |  禁止依存 43 本；EInfinity.Hammock.HammockValueComposition → EInfinity.Hammock.HammockValue |
| R65 | EInfinity.Hammock.HammockValueForward |  禁止依存 44 本；EInfinity.Hammock.HammockValueForward → EInfinity.Hammock.HammockValueComposition |
| R65 | EInfinity.Hammock.HammockValueRelative |  禁止依存 44 本；EInfinity.Hammock.HammockValueRelative → EInfinity.Hammock.HammockValue |
| R65 | EInfinity.Hammock.HomLiftColimit |  禁止依存 43 本；EInfinity.Hammock.HomLiftColimit → EInfinity.Hammock.HomLiftZigzag |
| R65 | EInfinity.Hammock.HomLiftZigzag |  禁止依存 42 本；EInfinity.Hammock.HomLiftZigzag → EInfinity.Hammock.ReducedColimit |
| R65 | EInfinity.Hammock.HomotopyWeakComparison |  禁止依存 60 本；EInfinity.Hammock.HomotopyWeakComparison → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.Hammock.IndexedSum |  禁止依存 80 本；EInfinity.Hammock.IndexedSum → EInfinity.Hammock.ValueSupportWeak |
| R65 | EInfinity.Hammock.IndexedSumIso |  禁止依存 81 本；EInfinity.Hammock.IndexedSumIso → EInfinity.Hammock.IndexedSum |
| R65 | EInfinity.Hammock.LeftRoofPrecomposeHomotopy |  禁止依存 14 本；EInfinity.Hammock.LeftRoofPrecomposeHomotopy → HA.Simplicial.AnodyneHomotopyLocalization → HA.Simplicial.AnodyneIntervalEndpoints → IC.ModelBridge.HA.FixedBoundaryExtensions |
| R65 | EInfinity.Hammock.LeftRoofPrefixCore |  禁止依存 30 本；EInfinity.Hammock.LeftRoofPrefixCore → EInfinity.Hammock.LeftRoofPrefixCylinder |
| R65 | EInfinity.Hammock.LeftRoofPrefixCoreNaturality |  禁止依存 31 本；EInfinity.Hammock.LeftRoofPrefixCoreNaturality → EInfinity.Hammock.LeftRoofPrefixCore |
| R65 | EInfinity.Hammock.LeftRoofPrefixCylinder |  禁止依存 29 本；EInfinity.Hammock.LeftRoofPrefixCylinder → EInfinity.Hammock.LeftRoofPrefixEndpoints |
| R65 | EInfinity.Hammock.LeftRoofPrefixEndpoints |  禁止依存 28 本；EInfinity.Hammock.LeftRoofPrefixEndpoints → EInfinity.Hammock.LeftRoofPrefixHomotopy |
| R65 | EInfinity.Hammock.LeftRoofPrefixHomotopy |  禁止依存 16 本；EInfinity.Hammock.LeftRoofPrefixHomotopy → EInfinity.Hammock.LeftRoofSameUniverseComparison |
| R65 | EInfinity.Hammock.LeftRoofPrefixNaturality |  禁止依存 32 本；EInfinity.Hammock.LeftRoofPrefixNaturality → EInfinity.Hammock.LeftRoofPrefixCoreNaturality |
| R65 | EInfinity.Hammock.LeftRoofPrefixPath |  禁止依存 33 本；EInfinity.Hammock.LeftRoofPrefixPath → EInfinity.Hammock.LeftRoofPrefixNaturality |
| R65 | EInfinity.Hammock.LeftRoofSameUniverseComparison |  禁止依存 15 本；EInfinity.Hammock.LeftRoofSameUniverseComparison → EInfinity.Hammock.LeftRoofPrecomposeHomotopy |
| R65 | EInfinity.Hammock.LengthBoundary |  禁止依存 24 本；EInfinity.Hammock.LengthBoundary → EInfinity.Hammock.ProperOverlap |
| R65 | EInfinity.Hammock.LengthBoundaryFiniteUnion |  禁止依存 76 本；EInfinity.Hammock.LengthBoundaryFiniteUnion → EInfinity.Hammock.LengthBoundary |
| R65 | EInfinity.Hammock.LengthBoundaryLift |  禁止依存 25 本；EInfinity.Hammock.LengthBoundaryLift → EInfinity.Hammock.LengthBoundary |
| R65 | EInfinity.Hammock.LengthBoundaryNaturality |  禁止依存 26 本；EInfinity.Hammock.LengthBoundaryNaturality → EInfinity.Hammock.LengthBoundaryLift |
| R65 | EInfinity.Hammock.LengthStagePushout |  禁止依存 28 本；EInfinity.Hammock.LengthStagePushout → EInfinity.Hammock.StageAttachmentDesc |
| R65 | EInfinity.Hammock.LocalizationValue |  禁止依存 43 本；EInfinity.Hammock.LocalizationValue → EInfinity.Hammock.HammockValue |
| R65 | EInfinity.Hammock.LocalizationValueNaturality |  禁止依存 44 本；EInfinity.Hammock.LocalizationValueNaturality → EInfinity.Hammock.LocalizationValue |
| R65 | EInfinity.Hammock.MarkedSpineComposition |  禁止依存 96 本；EInfinity.Hammock.MarkedSpineComposition → EInfinity.Hammock.AllMarkedCompositionPoints |
| R65 | EInfinity.Hammock.MarkedSpineCompositionLaws |  禁止依存 100 本；EInfinity.Hammock.MarkedSpineCompositionLaws → EInfinity.Hammock.AllMarkedUnitPoints |
| R65 | EInfinity.Hammock.MarkedSpineCompositionMaps |  禁止依存 97 本；EInfinity.Hammock.MarkedSpineCompositionMaps → EInfinity.Hammock.MarkedSpineComposition |
| R65 | EInfinity.Hammock.MarkedSpineDegreeCategory |  禁止依存 105 本；EInfinity.Hammock.MarkedSpineDegreeCategory → EInfinity.Hammock.MarkedSpineFoldUnique |
| R65 | EInfinity.Hammock.MarkedSpineEnrichedCategory |  禁止依存 101 本；EInfinity.Hammock.MarkedSpineEnrichedCategory → EInfinity.Hammock.MarkedSpineCompositionLaws |
| R65 | EInfinity.Hammock.MarkedSpineEnrichedFoldData |  禁止依存 108 本；EInfinity.Hammock.MarkedSpineEnrichedFoldData → EInfinity.Hammock.MarkedSpineEnrichedCategory |
| R65 | EInfinity.Hammock.MarkedSpineEnrichedFoldMap |  禁止依存 110 本；EInfinity.Hammock.MarkedSpineEnrichedFoldMap → EInfinity.Hammock.MarkedSpineEnrichedFoldPoints |
| R65 | EInfinity.Hammock.MarkedSpineEnrichedFoldPoints |  禁止依存 109 本；EInfinity.Hammock.MarkedSpineEnrichedFoldPoints → EInfinity.Hammock.MarkedSpineEnrichedFoldData |
| R65 | EInfinity.Hammock.MarkedSpineEnrichedFoldUnique |  禁止依存 111 本；EInfinity.Hammock.MarkedSpineEnrichedFoldUnique → EInfinity.Hammock.MarkedSpineEnrichedFoldMap |
| R65 | EInfinity.Hammock.MarkedSpineEnrichedRestriction |  禁止依存 113 本；EInfinity.Hammock.MarkedSpineEnrichedRestriction → EInfinity.Hammock.MarkedSpineEnrichedFoldUnique |
| R65 | EInfinity.Hammock.MarkedSpineEnrichedUniversal |  禁止依存 114 本；EInfinity.Hammock.MarkedSpineEnrichedUniversal → EInfinity.Hammock.MarkedSpineEnrichedRestriction |
| R65 | EInfinity.Hammock.MarkedSpineEvaluationWeak |  禁止依存 200 本；EInfinity.Hammock.MarkedSpineEvaluationWeak → EInfinity.Hammock.MarkedSpineGluingExtraction |
| R65 | EInfinity.Hammock.MarkedSpineExtraction |  禁止依存 65 本；EInfinity.Hammock.MarkedSpineExtraction → EInfinity.Hammock.MarkedSpineSimplex |
| R65 | EInfinity.Hammock.MarkedSpineExtractionComposition |  禁止依存 111 本；EInfinity.Hammock.MarkedSpineExtractionComposition → EInfinity.Hammock.MarkedSpineEnrichedFoldMap |
| R65 | EInfinity.Hammock.MarkedSpineExtractionGenerator |  禁止依存 112 本；EInfinity.Hammock.MarkedSpineExtractionGenerator → EInfinity.Hammock.MarkedSpineExtractionComposition |
| R65 | EInfinity.Hammock.MarkedSpineExtractionGluing |  禁止依存 70 本；EInfinity.Hammock.MarkedSpineExtractionGluing → EInfinity.Hammock.MarkedSpineGluing |
| R65 | EInfinity.Hammock.MarkedSpineFoldComposition |  禁止依存 102 本；EInfinity.Hammock.MarkedSpineFoldComposition → EInfinity.Hammock.MarkedSpineFoldData |
| R65 | EInfinity.Hammock.MarkedSpineFoldData |  禁止依存 101 本；EInfinity.Hammock.MarkedSpineFoldData → EInfinity.Hammock.MarkedSpineCompositionLaws |
| R65 | EInfinity.Hammock.MarkedSpineFoldSimplex |  禁止依存 105 本；EInfinity.Hammock.MarkedSpineFoldSimplex → EInfinity.Hammock.MarkedSpineFoldUnique |
| R65 | EInfinity.Hammock.MarkedSpineFoldTarget |  禁止依存 105 本；EInfinity.Hammock.MarkedSpineFoldTarget → EInfinity.Hammock.MarkedSpineFoldUnique |
| R65 | EInfinity.Hammock.MarkedSpineFoldUnique |  禁止依存 104 本；EInfinity.Hammock.MarkedSpineFoldUnique → EInfinity.Hammock.MarkedSpineFoldComposition |
| R65 | EInfinity.Hammock.MarkedSpineGeneratorPoint |  禁止依存 101 本；EInfinity.Hammock.MarkedSpineGeneratorPoint → EInfinity.Hammock.MarkedSpineCompositionLaws |
| R65 | EInfinity.Hammock.MarkedSpineGluing |  禁止依存 67 本；EInfinity.Hammock.MarkedSpineGluing → EInfinity.Hammock.MarkedSpineExtraction |
| R65 | EInfinity.Hammock.MarkedSpineGluingExtraction |  禁止依存 93 本；EInfinity.Hammock.MarkedSpineGluingExtraction → EInfinity.Hammock.MarkedSpineNativeRecovery |
| R65 | EInfinity.Hammock.MarkedSpineLocalizationEvaluation |  禁止依存 216 本；EInfinity.Hammock.MarkedSpineLocalizationEvaluation → EInfinity.Hammock.AllMarkedLocalizationValueComparison |
| R65 | EInfinity.Hammock.MarkedSpineMarkedComposition |  禁止依存 111 本；EInfinity.Hammock.MarkedSpineMarkedComposition → EInfinity.Hammock.MarkedSpineEnrichedFoldMap |
| R65 | EInfinity.Hammock.MarkedSpineNativeRecovery |  禁止依存 71 本；EInfinity.Hammock.MarkedSpineNativeRecovery → EInfinity.Hammock.MarkedSpineExtractionGluing |
| R65 | EInfinity.Hammock.MarkedSpineProducts |  禁止依存 135 本；EInfinity.Hammock.MarkedSpineProducts → EInfinity.Hammock.MarkedSpineSimplex |
| R65 | EInfinity.Hammock.MarkedSpineProductsIso |  禁止依存 136 本；EInfinity.Hammock.MarkedSpineProductsIso → EInfinity.Hammock.MarkedSpineProducts |
| R65 | EInfinity.Hammock.MarkedSpineSimplex |  禁止依存 64 本；EInfinity.Hammock.MarkedSpineSimplex → EInfinity.Hammock.UnmarkedMarkedSpine |
| R65 | EInfinity.Hammock.MarkedValueSpine |  禁止依存 168 本；EInfinity.Hammock.MarkedValueSpine → EInfinity.Hammock.AllMarkedEvaluationWeak |
| R65 | EInfinity.Hammock.MarkedValueSpineCategory |  禁止依存 170 本；EInfinity.Hammock.MarkedValueSpineCategory → EInfinity.Hammock.MarkedValueSpineComposition |
| R65 | EInfinity.Hammock.MarkedValueSpineComposition |  禁止依存 169 本；EInfinity.Hammock.MarkedValueSpineComposition → EInfinity.Hammock.MarkedValueSpine |
| R65 | EInfinity.Hammock.MarkedValueSpineCoreDescent |  禁止依存 172 本；EInfinity.Hammock.MarkedValueSpineCoreDescent → EInfinity.Hammock.MarkedValueSpineGenerators |
| R65 | EInfinity.Hammock.MarkedValueSpineDescent |  禁止依存 174 本；EInfinity.Hammock.MarkedValueSpineDescent → EInfinity.Hammock.MarkedValueSpineCoreDescent |
| R65 | EInfinity.Hammock.MarkedValueSpineDescentRecovery |  禁止依存 175 本；EInfinity.Hammock.MarkedValueSpineDescentRecovery → EInfinity.Hammock.MarkedValueSpineDescent |
| R65 | EInfinity.Hammock.MarkedValueSpineFold |  禁止依存 172 本；EInfinity.Hammock.MarkedValueSpineFold → EInfinity.Hammock.MarkedValueSpineGenerators |
| R65 | EInfinity.Hammock.MarkedValueSpineGenerators |  禁止依存 171 本；EInfinity.Hammock.MarkedValueSpineGenerators → EInfinity.Hammock.MarkedValueSpineCategory |
| R65 | EInfinity.Hammock.MarkedValueSpineLocalization |  禁止依存 175 本；EInfinity.Hammock.MarkedValueSpineLocalization → EInfinity.Hammock.MarkedValueSpineDescent |
| R65 | EInfinity.Hammock.MarkedValueSpineLocalizationEquivalence |  禁止依存 177 本；EInfinity.Hammock.MarkedValueSpineLocalizationEquivalence → EInfinity.Hammock.MarkedValueSpineLocalizationMarked |
| R65 | EInfinity.Hammock.MarkedValueSpineLocalizationHom |  禁止依存 178 本；EInfinity.Hammock.MarkedValueSpineLocalizationHom → EInfinity.Hammock.MarkedValueSpineLocalizationEquivalence |
| R65 | EInfinity.Hammock.MarkedValueSpineLocalizationMarked |  禁止依存 176 本；EInfinity.Hammock.MarkedValueSpineLocalizationMarked → EInfinity.Hammock.MarkedValueSpineLocalization |
| R65 | EInfinity.Hammock.MarkedValueSpineProductsIso |  禁止依存 169 本；EInfinity.Hammock.MarkedValueSpineProductsIso → EInfinity.Hammock.MarkedValueSpine |
| R65 | EInfinity.Hammock.MergeEraseConfluence |  禁止依存 30 本；EInfinity.Hammock.MergeEraseConfluence → EInfinity.Hammock.MergeEraseOverlap |
| R65 | EInfinity.Hammock.MergeEraseOverlap |  禁止依存 28 本；EInfinity.Hammock.MergeEraseOverlap → EInfinity.Hammock.PunctureSimplex |
| R65 | EInfinity.Hammock.MergeEraseSquare |  禁止依存 28 本；EInfinity.Hammock.MergeEraseSquare → EInfinity.Hammock.PunctureSimplex |
| R65 | EInfinity.Hammock.MergeMergeConfluence |  禁止依存 25 本；EInfinity.Hammock.MergeMergeConfluence → EInfinity.Hammock.Reduction |
| R65 | EInfinity.Hammock.MiddleBackwardErasureIso |  禁止依存 98 本；EInfinity.Hammock.MiddleBackwardErasureIso → EInfinity.Hammock.MiddleBackwardIdentityInsertionComparison |
| R65 | EInfinity.Hammock.MiddleBackwardExtractLegRecovery |  禁止依存 24 本；EInfinity.Hammock.MiddleBackwardExtractLegRecovery → EInfinity.Hammock.MiddleBackwardExtractFamily |
| R65 | EInfinity.Hammock.MiddleBackwardExtractPaths |  禁止依存 22 本；EInfinity.Hammock.MiddleBackwardExtractPaths → EInfinity.Hammock.MiddleBackwardPositions |
| R65 | EInfinity.Hammock.MiddleBackwardMovingExtractPaths |  禁止依存 23 本；EInfinity.Hammock.MiddleBackwardMovingExtractPaths → EInfinity.Hammock.MiddleBackwardExtractPaths |
| R65 | EInfinity.Hammock.MiddleBackwardPositionCases |  禁止依存 22 本；EInfinity.Hammock.MiddleBackwardPositionCases → EInfinity.Hammock.MiddleBackwardPositions |
| R65 | EInfinity.Hammock.MiddleBackwardPositions |  禁止依存 21 本；EInfinity.Hammock.MiddleBackwardPositions → EInfinity.Hammock.MiddleBackwardFamilyReplacementComparisons |
| R65 | EInfinity.Hammock.MixedRelativeColimitMap |  禁止依存 43 本；EInfinity.Hammock.MixedRelativeColimitMap → EInfinity.Hammock.RelativeColimitMap |
| R65 | EInfinity.Hammock.MixedRelativeComposition |  禁止依存 44 本；EInfinity.Hammock.MixedRelativeComposition → EInfinity.Hammock.MixedRelativeColimitMap |
| R65 | EInfinity.Hammock.MixedRelativePointActions |  禁止依存 46 本；EInfinity.Hammock.MixedRelativePointActions → EInfinity.Hammock.MixedRelativeComposition |
| R65 | EInfinity.Hammock.NerveEmbedding |  禁止依存 20 本；EInfinity.Hammock.NerveEmbedding → EInfinity.FrameHom.NerveAsSmall |
| R65 | EInfinity.Hammock.NerveWeakTransport |  禁止依存 63 本；EInfinity.Hammock.NerveWeakTransport → IC.F2.FilteredExchange.OppositeWeakHomotopy |
| R65 | EInfinity.Hammock.NormalForm |  禁止依存 38 本；EInfinity.Hammock.NormalForm → EInfinity.Hammock.ReductionConfluence |
| R65 | EInfinity.Hammock.NormalFormTransition |  禁止依存 39 本；EInfinity.Hammock.NormalFormTransition → EInfinity.Hammock.EraseEmbedding |
| R65 | EInfinity.Hammock.ProperDiagram |  禁止依存 22 本；EInfinity.Hammock.ProperDiagram → EInfinity.Hammock.GraphEmbedding |
| R65 | EInfinity.Hammock.ProperFractionDiagrams |  禁止依存 75 本；EInfinity.Hammock.ProperFractionDiagrams → EInfinity.Hammock.ProperPrecomposition |
| R65 | EInfinity.Hammock.ProperOverlap |  禁止依存 23 本；EInfinity.Hammock.ProperOverlap → EInfinity.Hammock.ProperDiagram |
| R65 | EInfinity.Hammock.ProperPrecomposition |  禁止依存 74 本；EInfinity.Hammock.ProperPrecomposition → EInfinity.Hammock.ProperSubsetImages |
| R65 | EInfinity.Hammock.ProperSubsetImages |  禁止依存 73 本；EInfinity.Hammock.ProperSubsetImages → EInfinity.Hammock.ProperDiagram |
| R65 | EInfinity.Hammock.PunctureSimplex |  禁止依存 27 本；EInfinity.Hammock.PunctureSimplex → EInfinity.Hammock.EraseEmbedding |
| R65 | EInfinity.Hammock.QuiverTreeCollapseWeakComparison |  禁止依存 96 本；EInfinity.Hammock.QuiverTreeCollapseWeakComparison → EInfinity.Hammock.RelativeFunctorLaws |
| R65 | EInfinity.Hammock.QuiverTreeFiniteContractible |  禁止依存 101 本；EInfinity.Hammock.QuiverTreeFiniteContractible → EInfinity.Hammock.QuiverTreeLeafContractible |
| R65 | EInfinity.Hammock.QuiverTreeFiniteWeakMaps |  禁止依存 103 本；EInfinity.Hammock.QuiverTreeFiniteWeakMaps → EInfinity.Hammock.ContractibleMaps |
| R65 | EInfinity.Hammock.QuiverTreeLeafContractible |  禁止依存 98 本；EInfinity.Hammock.QuiverTreeLeafContractible → EInfinity.Hammock.QuiverTreeCollapseWeakComparison |
| R65 | EInfinity.Hammock.QuiverTreeRootContractible |  禁止依存 61 本；EInfinity.Hammock.QuiverTreeRootContractible → EInfinity.Hammock.SubsingletonCategoryContractible |
| R65 | EInfinity.Hammock.RawEmbeddingComparison |  禁止依存 22 本；EInfinity.Hammock.RawEmbeddingComparison → EInfinity.Hammock.GraphEmbedding |
| R65 | EInfinity.Hammock.ReducedColimit |  禁止依存 41 本；EInfinity.Hammock.ReducedColimit → EInfinity.Hammock.NormalFormTransition |
| R65 | EInfinity.Hammock.ReducedPointActions |  禁止依存 42 本；EInfinity.Hammock.ReducedPointActions → EInfinity.Hammock.ReducedColimit |
| R65 | EInfinity.Hammock.ReducedSimplicialSet |  禁止依存 39 本；EInfinity.Hammock.ReducedSimplicialSet → EInfinity.Hammock.NormalForm |
| R65 | EInfinity.Hammock.Reduction |  禁止依存 24 本；EInfinity.Hammock.Reduction → EInfinity.Hammock.EraseSimplex |
| R65 | EInfinity.Hammock.ReductionConfluence |  禁止依存 35 本；EInfinity.Hammock.ReductionConfluence → EInfinity.Hammock.EraseEraseConfluence |
| R65 | EInfinity.Hammock.ReductionExistence |  禁止依存 25 本；EInfinity.Hammock.ReductionExistence → EInfinity.Hammock.Reduction |
| R65 | EInfinity.Hammock.ReductionNaturality |  禁止依存 26 本；EInfinity.Hammock.ReductionNaturality → EInfinity.Hammock.EraseSimplexNaturality |
| R65 | EInfinity.Hammock.RelativeColimitMap |  禁止依存 42 本；EInfinity.Hammock.RelativeColimitMap → EInfinity.Hammock.ReducedColimit |
| R65 | EInfinity.Hammock.RelativeCompositionPoints |  禁止依存 43 本；EInfinity.Hammock.RelativeCompositionPoints → EInfinity.Hammock.RelativeColimitMap |
| R65 | EInfinity.Hammock.RelativeEquivalenceUnitWeak |  禁止依存 98 本；EInfinity.Hammock.RelativeEquivalenceUnitWeak → EInfinity.Hammock.RelativeEquivalenceWeak |
| R65 | EInfinity.Hammock.RelativeEquivalenceWeak |  禁止依存 97 本；EInfinity.Hammock.RelativeEquivalenceWeak → EInfinity.Hammock.RelativeFunctorLaws |
| R65 | EInfinity.Hammock.RelativeFixedArrow |  禁止依存 46 本；EInfinity.Hammock.RelativeFixedArrow → EInfinity.Hammock.RelativeFixedColimitMap |
| R65 | EInfinity.Hammock.RelativeFixedColimitMap |  禁止依存 44 本；EInfinity.Hammock.RelativeFixedColimitMap → EInfinity.Hammock.RelativeCompositionPoints |
| R65 | EInfinity.Hammock.RelativeFixedUnit |  禁止依存 46 本；EInfinity.Hammock.RelativeFixedUnit → EInfinity.Hammock.RelativeFixedColimitMap |
| R65 | EInfinity.Hammock.RelativeForwardSimplex |  禁止依存 44 本；EInfinity.Hammock.RelativeForwardSimplex → EInfinity.Hammock.RelativeCompositionPoints |
| R65 | EInfinity.Hammock.RelativeFunctorLaws |  禁止依存 43 本；EInfinity.Hammock.RelativeFunctorLaws → EInfinity.Hammock.RelativeColimitMap |
| R65 | EInfinity.Hammock.RelativeNaturalColimitHomotopy |  禁止依存 45 本；EInfinity.Hammock.RelativeNaturalColimitHomotopy → EInfinity.Hammock.RelativeNaturalMapRecovery |
| R65 | EInfinity.Hammock.RelativeNaturalMapRecovery |  禁止依存 44 本；EInfinity.Hammock.RelativeNaturalMapRecovery → EInfinity.Hammock.RelativeCompositionPoints |
| R65 | EInfinity.Hammock.RelativeNaturalWeakComparison |  禁止依存 94 本；EInfinity.Hammock.RelativeNaturalWeakComparison → EInfinity.Hammock.HomotopyWeakComparison |
| R65 | EInfinity.Hammock.RootedFiniteContractible |  禁止依存 118 本；EInfinity.Hammock.RootedFiniteContractible → EInfinity.Hammock.QuiverTreeFiniteContractible |
| R65 | EInfinity.Hammock.RootedFiniteGraphColimit |  禁止依存 104 本；EInfinity.Hammock.RootedFiniteGraphColimit → EInfinity.Hammock.RootedFiniteSimplexLift |
| R65 | EInfinity.Hammock.RootedFiniteGraphColimitNaturality |  禁止依存 105 本；EInfinity.Hammock.RootedFiniteGraphColimitNaturality → EInfinity.Hammock.RootedFiniteGraphColimit |
| R65 | EInfinity.Hammock.RootedFiniteHammockColimit |  禁止依存 106 本；EInfinity.Hammock.RootedFiniteHammockColimit → EInfinity.Hammock.RootedFiniteGraphColimitNaturality |
| R65 | EInfinity.Hammock.RootedFiniteSimplexLift |  禁止依存 103 本；EInfinity.Hammock.RootedFiniteSimplexLift → EInfinity.Hammock.FiniteGridRootHull |
| R65 | EInfinity.Hammock.SingleZigzagDiagonalEvaluation |  禁止依存 168 本；EInfinity.Hammock.SingleZigzagDiagonalEvaluation → EInfinity.Hammock.DoubleSimplicialWeak |
| R65 | EInfinity.Hammock.SingleZigzagGraphValue |  禁止依存 64 本；EInfinity.Hammock.SingleZigzagGraphValue → EInfinity.Hammock.NerveWeakTransport |
| R65 | EInfinity.Hammock.SingleZigzagHomDiagram |  禁止依存 65 本；EInfinity.Hammock.SingleZigzagHomDiagram → EInfinity.Hammock.SingleZigzagGraphValue |
| R65 | EInfinity.Hammock.StageAttachmentData |  禁止依存 26 本；EInfinity.Hammock.StageAttachmentData → EInfinity.Hammock.LengthBoundaryLift |
| R65 | EInfinity.Hammock.StageAttachmentDesc |  禁止依存 27 本；EInfinity.Hammock.StageAttachmentDesc → EInfinity.Hammock.StageAttachmentData |
| R65 | EInfinity.Hammock.StagePushoutNaturality |  禁止依存 30 本；EInfinity.Hammock.StagePushoutNaturality → EInfinity.Hammock.LengthBoundaryNaturality |
| R65 | EInfinity.Hammock.SubsingletonCategoryContractible |  禁止依存 60 本；EInfinity.Hammock.SubsingletonCategoryContractible → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.Hammock.TopEquivalenceWeak |  禁止依存 97 本；EInfinity.Hammock.TopEquivalenceWeak → EInfinity.Hammock.RelativeFunctorLaws |
| R65 | EInfinity.Hammock.TransfunctorTwoSidedDiagram |  禁止依存 204 本；EInfinity.Hammock.TransfunctorTwoSidedDiagram → EInfinity.Hammock.TwoSidedDiagramBar |
| R65 | EInfinity.Hammock.TransfunctorTwoSidedMap |  禁止依存 205 本；EInfinity.Hammock.TransfunctorTwoSidedMap → EInfinity.Hammock.TransfunctorTwoSidedDiagram |
| R65 | EInfinity.Hammock.TwoIndexCoproduct |  禁止依存 62 本；EInfinity.Hammock.TwoIndexCoproduct → EInfinity.Hammock.WeakPushoutGluing |
| R65 | EInfinity.Hammock.TwoSidedBarRows |  禁止依存 81 本；EInfinity.Hammock.TwoSidedBarRows → EInfinity.Hammock.IndexedSum |
| R65 | EInfinity.Hammock.TwoSidedBarWeak |  禁止依存 195 本；EInfinity.Hammock.TwoSidedBarWeak → EInfinity.Hammock.DoubleSimplicialColumnWeak |
| R65 | EInfinity.Hammock.TwoSidedDiagramBar |  禁止依存 203 本；EInfinity.Hammock.TwoSidedDiagramBar → EInfinity.Hammock.TwoSidedDiagramTotal |
| R65 | EInfinity.Hammock.TwoSidedDiagramDiagonal |  禁止依存 204 本；EInfinity.Hammock.TwoSidedDiagramDiagonal → EInfinity.Hammock.DoubleSimplicialWeak |
| R65 | EInfinity.Hammock.TwoSidedDiagramDiagonalLabels |  禁止依存 209 本；EInfinity.Hammock.TwoSidedDiagramDiagonalLabels → EInfinity.Hammock.TwoSidedDiagramPartialRows |
| R65 | EInfinity.Hammock.TwoSidedDiagramDiagonalMap |  禁止依存 205 本；EInfinity.Hammock.TwoSidedDiagramDiagonalMap → EInfinity.Hammock.TwoSidedDiagramDiagonal |
| R65 | EInfinity.Hammock.TwoSidedDiagramFixedVertexFibers |  禁止依存 233 本；EInfinity.Hammock.TwoSidedDiagramFixedVertexFibers → EInfinity.Hammock.IndexedSum |
| R65 | EInfinity.Hammock.TwoSidedDiagramFixedVertices |  禁止依存 210 本；EInfinity.Hammock.TwoSidedDiagramFixedVertices → EInfinity.Hammock.TwoSidedDiagramDiagonalLabels |
| R65 | EInfinity.Hammock.TwoSidedDiagramLabelComparison |  禁止依存 210 本；EInfinity.Hammock.TwoSidedDiagramLabelComparison → EInfinity.Hammock.TwoSidedDiagramDiagonalLabels |
| R65 | EInfinity.Hammock.TwoSidedDiagramPartialRows |  禁止依存 208 本；EInfinity.Hammock.TwoSidedDiagramPartialRows → EInfinity.Hammock.DoubleSimplicialColumnWeak |
| R65 | EInfinity.Hammock.TwoSidedDiagramRows |  禁止依存 204 本；EInfinity.Hammock.TwoSidedDiagramRows → EInfinity.Hammock.TwoSidedDiagramBar |
| R65 | EInfinity.Hammock.TwoSidedDiagramSimplicialWeak |  禁止依存 244 本；EInfinity.Hammock.TwoSidedDiagramSimplicialWeak → EInfinity.Hammock.TwoSidedDiagramVertexProductMap |
| R65 | EInfinity.Hammock.TwoSidedDiagramSimplicialWeakSpecializations |  禁止依存 246 本；EInfinity.Hammock.TwoSidedDiagramSimplicialWeakSpecializations → EInfinity.Hammock.TwoSidedDiagramSimplicialWeak |
| R65 | EInfinity.Hammock.TwoSidedDiagramTotal |  禁止依存 202 本；EInfinity.Hammock.TwoSidedDiagramTotal → EInfinity.Hammock.TwoSidedThomasonTransition |
| R65 | EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap |  禁止依存 239 本；EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap → EInfinity.Hammock.TwoSidedDiagramVertexProducts |
| R65 | EInfinity.Hammock.TwoSidedDiagramVertexHomMap |  禁止依存 239 本；EInfinity.Hammock.TwoSidedDiagramVertexHomMap → EInfinity.Hammock.TwoSidedDiagramVertexProducts |
| R65 | EInfinity.Hammock.TwoSidedDiagramVertexMapSpecializations |  禁止依存 241 本；EInfinity.Hammock.TwoSidedDiagramVertexMapSpecializations → EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap |
| R65 | EInfinity.Hammock.TwoSidedDiagramVertexProductMap |  禁止依存 242 本；EInfinity.Hammock.TwoSidedDiagramVertexProductMap → EInfinity.Hammock.TwoSidedDiagramLabelComparison |
| R65 | EInfinity.Hammock.TwoSidedDiagramVertexProducts |  禁止依存 238 本；EInfinity.Hammock.TwoSidedDiagramVertexProducts → EInfinity.Hammock.FiniteProduct |
| R65 | EInfinity.Hammock.TwoSidedGrothendieckCoefficientWeak |  禁止依存 187 本；EInfinity.Hammock.TwoSidedGrothendieckCoefficientWeak → EInfinity.Hammock.NerveWeakTransport |
| R65 | EInfinity.Hammock.TwoSidedGrothendieckLeftComparison |  禁止依存 181 本；EInfinity.Hammock.TwoSidedGrothendieckLeftComparison → EInfinity.Hammock.TwoSidedGrothendieckRightWeak |
| R65 | EInfinity.Hammock.TwoSidedGrothendieckRightWeak |  禁止依存 180 本；EInfinity.Hammock.TwoSidedGrothendieckRightWeak → EInfinity.Hammock.GrothendieckPointwiseWeak |
| R65 | EInfinity.Hammock.TwoSidedMixedLabelNaturality |  禁止依存 64 本；EInfinity.Hammock.TwoSidedMixedLabelNaturality → EInfinity.Hammock.NerveWeakTransport |
| R65 | EInfinity.Hammock.TwoSidedThomasonArrows |  禁止依存 84 本；EInfinity.Hammock.TwoSidedThomasonArrows → EInfinity.FrameHom.ThomasonSimplex |
| R65 | EInfinity.Hammock.TwoSidedThomasonBaseChange |  禁止依存 92 本；EInfinity.Hammock.TwoSidedThomasonBaseChange → EInfinity.Hammock.TwoSidedBarBaseChange |
| R65 | EInfinity.Hammock.TwoSidedThomasonLeftFactorization |  禁止依存 208 本；EInfinity.Hammock.TwoSidedThomasonLeftFactorization → EInfinity.Hammock.TwoSidedThomasonNerveMap |
| R65 | EInfinity.Hammock.TwoSidedThomasonNaturality |  禁止依存 89 本；EInfinity.Hammock.TwoSidedThomasonNaturality → EInfinity.Hammock.TwoSidedGrothendieckCoefficientComponents |
| R65 | EInfinity.Hammock.TwoSidedThomasonNerveMap |  禁止依存 86 本；EInfinity.Hammock.TwoSidedThomasonNerveMap → EInfinity.Hammock.TwoSidedThomasonSimplex |
| R65 | EInfinity.Hammock.TwoSidedThomasonRightForget |  禁止依存 208 本；EInfinity.Hammock.TwoSidedThomasonRightForget → EInfinity.FrameHom.ThomasonNerveMap |
| R65 | EInfinity.Hammock.TwoSidedThomasonSimplex |  禁止依存 85 本；EInfinity.Hammock.TwoSidedThomasonSimplex → EInfinity.Hammock.TwoSidedThomasonArrows |
| R65 | EInfinity.Hammock.TwoSidedThomasonTransition |  禁止依存 1184 本；EInfinity.Hammock.TwoSidedThomasonTransition → EInfinity.Hammock.TwoSidedThomasonBaseChange |
| R65 | EInfinity.Hammock.TwoSidedThomasonWeak |  禁止依存 1178 本；EInfinity.Hammock.TwoSidedThomasonWeak → EInfinity.Hammock.DoubleSimplicialWeak |
| R65 | EInfinity.Hammock.TwoSidedWeightedLeftMap |  禁止依存 74 本；EInfinity.Hammock.TwoSidedWeightedLeftMap → EInfinity.Hammock.ContravariantThomasonSimplex |
| R65 | EInfinity.Hammock.TwoSidedWeightedLeftRows |  禁止依存 129 本；EInfinity.Hammock.TwoSidedWeightedLeftRows → EInfinity.FrameHom.ThomasonNerveMap |
| R65 | EInfinity.Hammock.TwoSidedWeightedLeftSourceCalculation |  禁止依存 134 本；EInfinity.Hammock.TwoSidedWeightedLeftSourceCalculation → EInfinity.FrameHom.ThomasonNerveMap |
| R65 | EInfinity.Hammock.TwoSidedWeightedLeftSourceIso |  禁止依存 79 本；EInfinity.Hammock.TwoSidedWeightedLeftSourceIso → EInfinity.Hammock.TwoSidedWeightedLeftSourceRows |
| R65 | EInfinity.Hammock.TwoSidedWeightedLeftSourceRows |  禁止依存 78 本；EInfinity.Hammock.TwoSidedWeightedLeftSourceRows → EInfinity.Hammock.TwoSidedWeightedLeftMap |
| R65 | EInfinity.Hammock.TwoSidedWeightedLeftWeak |  禁止依存 190 本；EInfinity.Hammock.TwoSidedWeightedLeftWeak → EInfinity.FrameHom.ThomasonInversion |
| R65 | EInfinity.Hammock.UniverseValue |  禁止依存 43 本；EInfinity.Hammock.UniverseValue → EInfinity.Hammock.HammockValue |
| R65 | EInfinity.Hammock.UnmarkedCompositionValue |  禁止依存 48 本；EInfinity.Hammock.UnmarkedCompositionValue → EInfinity.Hammock.UnmarkedNonemptyImage |
| R65 | EInfinity.Hammock.UnmarkedCutPasteRecovery |  禁止依存 52 本；EInfinity.Hammock.UnmarkedCutPasteRecovery → EInfinity.Hammock.UnmarkedFirstFactorPasteRecovery |
| R65 | EInfinity.Hammock.UnmarkedCutRecursion |  禁止依存 54 本；EInfinity.Hammock.UnmarkedCutRecursion → EInfinity.Hammock.UnmarkedCutResidualLength |
| R65 | EInfinity.Hammock.UnmarkedCutResidualLength |  禁止依存 53 本；EInfinity.Hammock.UnmarkedCutResidualLength → EInfinity.Hammock.UnmarkedCutValueRecovery |
| R65 | EInfinity.Hammock.UnmarkedCutSpine |  禁止依存 55 本；EInfinity.Hammock.UnmarkedCutSpine → EInfinity.Hammock.UnmarkedCutRecursion |
| R65 | EInfinity.Hammock.UnmarkedCutValueRecovery |  禁止依存 52 本；EInfinity.Hammock.UnmarkedCutValueRecovery → EInfinity.Hammock.UnmarkedFactorTargetValue |
| R65 | EInfinity.Hammock.UnmarkedEmptySpace |  禁止依存 51 本；EInfinity.Hammock.UnmarkedEmptySpace → EInfinity.Hammock.AllMarkedImage |
| R65 | EInfinity.Hammock.UnmarkedFactorPaste |  禁止依存 44 本；EInfinity.Hammock.UnmarkedFactorPaste → EInfinity.Hammock.AllMarkedNative |
| R65 | EInfinity.Hammock.UnmarkedFactorPasteValue |  禁止依存 57 本；EInfinity.Hammock.UnmarkedFactorPasteValue → EInfinity.Hammock.AllMarkedImage |
| R65 | EInfinity.Hammock.UnmarkedFactorTargetValue |  禁止依存 44 本；EInfinity.Hammock.UnmarkedFactorTargetValue → EInfinity.Hammock.UnmarkedGeneratorValue |
| R65 | EInfinity.Hammock.UnmarkedFirstFactorPasteRecovery |  禁止依存 45 本；EInfinity.Hammock.UnmarkedFirstFactorPasteRecovery → EInfinity.Hammock.UnmarkedFactorPaste |
| R65 | EInfinity.Hammock.UnmarkedFirstFactorValue |  禁止依存 47 本；EInfinity.Hammock.UnmarkedFirstFactorValue → EInfinity.Hammock.UnmarkedValueAppend |
| R65 | EInfinity.Hammock.UnmarkedFreeEnrichedFunctor |  禁止依存 122 本；EInfinity.Hammock.UnmarkedFreeEnrichedFunctor → EInfinity.Hammock.FreeHammockEnrichedUniversal |
| R65 | EInfinity.Hammock.UnmarkedGeneratorValue |  禁止依存 43 本；EInfinity.Hammock.UnmarkedGeneratorValue → EInfinity.Hammock.HammockValue |
| R65 | EInfinity.Hammock.UnmarkedMarkedSpine |  禁止依存 63 本；EInfinity.Hammock.UnmarkedMarkedSpine → EInfinity.Hammock.AllMarkedEmptyIso |
| R65 | EInfinity.Hammock.UnmarkedNonemptyCutInclusion |  禁止依存 48 本；EInfinity.Hammock.UnmarkedNonemptyCutInclusion → EInfinity.Hammock.UnmarkedNonemptyIso |
| R65 | EInfinity.Hammock.UnmarkedNonemptyImage |  禁止依存 45 本；EInfinity.Hammock.UnmarkedNonemptyImage → EInfinity.Hammock.UnmarkedValueNonempty |
| R65 | EInfinity.Hammock.UnmarkedNonemptyIso |  禁止依存 47 本；EInfinity.Hammock.UnmarkedNonemptyIso → EInfinity.Hammock.UnmarkedNonemptySpace |
| R65 | EInfinity.Hammock.UnmarkedNonemptySpace |  禁止依存 46 本；EInfinity.Hammock.UnmarkedNonemptySpace → EInfinity.Hammock.UnmarkedNonemptyImage |
| R65 | EInfinity.Hammock.UnmarkedPasteCutRecovery |  禁止依存 77 本；EInfinity.Hammock.UnmarkedPasteCutRecovery → EInfinity.Hammock.UnmarkedFactorPasteValue |
| R65 | EInfinity.Hammock.UnmarkedPastedAfterData |  禁止依存 62 本；EInfinity.Hammock.UnmarkedPastedAfterData → EInfinity.Hammock.UnmarkedPastedBeforeData |
| R65 | EInfinity.Hammock.UnmarkedPastedAmbientRecovery |  禁止依存 71 本；EInfinity.Hammock.UnmarkedPastedAmbientRecovery → EInfinity.Hammock.UnmarkedPastedIdentityFunctors |
| R65 | EInfinity.Hammock.UnmarkedPastedBeforeData |  禁止依存 61 本；EInfinity.Hammock.UnmarkedPastedBeforeData → EInfinity.Hammock.UnmarkedPastedSimplex |
| R65 | EInfinity.Hammock.UnmarkedPastedBlockDiagrams |  禁止依存 66 本；EInfinity.Hammock.UnmarkedPastedBlockDiagrams → EInfinity.Hammock.UnmarkedPastedAfterData |
| R65 | EInfinity.Hammock.UnmarkedPastedColumn |  禁止依存 47 本；EInfinity.Hammock.UnmarkedPastedColumn → EInfinity.Hammock.UnmarkedValueAppend |
| R65 | EInfinity.Hammock.UnmarkedPastedCutLength |  禁止依存 60 本；EInfinity.Hammock.UnmarkedPastedCutLength → EInfinity.Hammock.UnmarkedPastedSimplex |
| R65 | EInfinity.Hammock.UnmarkedPastedGeneratorRecovery |  禁止依存 62 本；EInfinity.Hammock.UnmarkedPastedGeneratorRecovery → EInfinity.Hammock.UnmarkedCutResidualLength |
| R65 | EInfinity.Hammock.UnmarkedPastedIdentityBlocks |  禁止依存 68 本；EInfinity.Hammock.UnmarkedPastedIdentityBlocks → EInfinity.Hammock.UnmarkedPastedSelectedBlocks |
| R65 | EInfinity.Hammock.UnmarkedPastedIdentityDiagrams |  禁止依存 69 本；EInfinity.Hammock.UnmarkedPastedIdentityDiagrams → EInfinity.Hammock.UnmarkedPastedIdentityBlocks |
| R65 | EInfinity.Hammock.UnmarkedPastedIdentityFunctors |  禁止依存 70 本；EInfinity.Hammock.UnmarkedPastedIdentityFunctors → EInfinity.Hammock.UnmarkedPastedIdentityDiagrams |
| R65 | EInfinity.Hammock.UnmarkedPastedInclusion |  禁止依存 60 本；EInfinity.Hammock.UnmarkedPastedInclusion → EInfinity.Hammock.UnmarkedPastedSimplex |
| R65 | EInfinity.Hammock.UnmarkedPastedJoints |  禁止依存 62 本；EInfinity.Hammock.UnmarkedPastedJoints → EInfinity.Hammock.UnmarkedPastedZeroAttachments |
| R65 | EInfinity.Hammock.UnmarkedPastedNativeRecovery |  禁止依存 73 本；EInfinity.Hammock.UnmarkedPastedNativeRecovery → EInfinity.Hammock.AllMarkedEmbedding |
| R65 | EInfinity.Hammock.UnmarkedPastedSelectedBlocks |  禁止依存 67 本；EInfinity.Hammock.UnmarkedPastedSelectedBlocks → EInfinity.Hammock.UnmarkedPastedBlockDiagrams |
| R65 | EInfinity.Hammock.UnmarkedPastedSimplex |  禁止依存 59 本；EInfinity.Hammock.UnmarkedPastedSimplex → EInfinity.Hammock.UnmarkedFactorPasteValue |
| R65 | EInfinity.Hammock.UnmarkedPastedWordSplit |  禁止依存 48 本；EInfinity.Hammock.UnmarkedPastedWordSplit → EInfinity.Hammock.UnmarkedPastedColumn |
| R65 | EInfinity.Hammock.UnmarkedPastedZeroAttachments |  禁止依存 61 本；EInfinity.Hammock.UnmarkedPastedZeroAttachments → EInfinity.Hammock.UnmarkedPastedCutLength |
| R65 | EInfinity.Hammock.UnmarkedValueAppend |  禁止依存 46 本；EInfinity.Hammock.UnmarkedValueAppend → EInfinity.Hammock.UnmarkedValueFlatten |
| R65 | EInfinity.Hammock.UnmarkedValueFlatten |  禁止依存 45 本；EInfinity.Hammock.UnmarkedValueFlatten → EInfinity.Hammock.UnmarkedValueNonempty |
| R65 | EInfinity.Hammock.UnmarkedValueNonempty |  禁止依存 44 本；EInfinity.Hammock.UnmarkedValueNonempty → EInfinity.Hammock.UnmarkedGeneratorValue |
| R65 | EInfinity.Hammock.ValueSupportDiagram |  禁止依存 65 本；EInfinity.Hammock.ValueSupportDiagram → EInfinity.Hammock.ValueSupportSubcomplex |
| R65 | EInfinity.Hammock.ValueSupportFiniteWeak |  禁止依存 65 本；EInfinity.Hammock.ValueSupportFiniteWeak → EInfinity.Hammock.ValueSupportSubcomplex |
| R65 | EInfinity.Hammock.ValueSupportSingletonWeak |  禁止依存 66 本；EInfinity.Hammock.ValueSupportSingletonWeak → EInfinity.Hammock.ValueSupportFiniteWeak |
| R65 | EInfinity.Hammock.ValueSupportSubcomplex |  禁止依存 64 本；EInfinity.Hammock.ValueSupportSubcomplex → EInfinity.Hammock.WeakFiniteUnion |
| R65 | EInfinity.Hammock.ValueSupportWeak |  禁止依存 79 本；EInfinity.Hammock.ValueSupportWeak → EInfinity.Hammock.ValueSupportDiagram |
| R65 | EInfinity.Hammock.WeakAnodyneLocalization |  禁止依存 60 本；EInfinity.Hammock.WeakAnodyneLocalization → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.Hammock.WeakArrowActionEquivalences |  禁止依存 60 本；EInfinity.Hammock.WeakArrowActionEquivalences → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.Hammock.WeakFiniteSubsetColimit |  禁止依存 69 本；EInfinity.Hammock.WeakFiniteSubsetColimit → EInfinity.Hammock.WeakSequentialColimit |
| R65 | EInfinity.Hammock.WeakFiniteUnion |  禁止依存 63 本；EInfinity.Hammock.WeakFiniteUnion → EInfinity.Hammock.WeakUnionGluing |
| R65 | EInfinity.Hammock.WeakIndexedSum |  禁止依存 81 本；EInfinity.Hammock.WeakIndexedSum → EInfinity.Hammock.IndexedSum |
| R65 | EInfinity.Hammock.WeakLengthBoundary |  禁止依存 80 本；EInfinity.Hammock.WeakLengthBoundary → EInfinity.Hammock.LengthBoundaryFiniteUnion |
| R65 | EInfinity.Hammock.WeakLengthStages |  禁止依存 87 本；EInfinity.Hammock.WeakLengthStages → EInfinity.Hammock.WeakStageSuccessor |
| R65 | EInfinity.Hammock.WeakProperColimit |  禁止依存 98 本；EInfinity.Hammock.WeakProperColimit → EInfinity.Hammock.WeakLengthStages |
| R65 | EInfinity.Hammock.WeakPushout |  禁止依存 59 本；EInfinity.Hammock.WeakPushout → IC.F1.Yoneda.PresheafDensity.Support.WeakHomotopyPrecomposition → IC.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakFunctoriality → IC.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence → IC.HomotopyLimits.KanSourceReplacement → HA.Simplicial.AnodyneKanReplacement → IC.ModelBridge.HA.Generators |
| R65 | EInfinity.Hammock.WeakPushoutGluing |  禁止依存 61 本；EInfinity.Hammock.WeakPushoutGluing → EInfinity.Hammock.WeakUnderPushout |
| R65 | EInfinity.Hammock.WeakRange |  禁止依存 63 本；EInfinity.Hammock.WeakRange → EInfinity.Hammock.WeakUnionGluing |
| R65 | EInfinity.Hammock.WeakSequentialColimit |  禁止依存 68 本；EInfinity.Hammock.WeakSequentialColimit → IC.F2.FilteredExchange.FilteredPointwiseWeakEquivalences |
| R65 | EInfinity.Hammock.WeakStageSuccessor |  禁止依存 86 本；EInfinity.Hammock.WeakStageSuccessor → EInfinity.Hammock.StagePushoutNaturality |
| R65 | EInfinity.Hammock.WeakTensor |  禁止依存 60 本；EInfinity.Hammock.WeakTensor → IC.F2.FilteredExchange.ContinuousKanProductUnit |
| R65 | EInfinity.Hammock.WeakTwoOfSix |  禁止依存 60 本；EInfinity.Hammock.WeakTwoOfSix → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.Hammock.WeakUnderPushout |  禁止依存 60 本；EInfinity.Hammock.WeakUnderPushout → EInfinity.Hammock.WeakPushout |
| R65 | EInfinity.Hammock.WeakUnionGluing |  禁止依存 62 本；EInfinity.Hammock.WeakUnionGluing → EInfinity.Hammock.WeakPushoutGluing |
| R65 | EInfinity.Hammock.WordBackwardBlockDirections |  禁止依存 24 本；EInfinity.Hammock.WordBackwardBlockDirections → EInfinity.Hammock.WordBackwardBlocks |
| R65 | EInfinity.Hammock.WordBackwardBlocks |  禁止依存 23 本；EInfinity.Hammock.WordBackwardBlocks → EInfinity.Hammock.MiddleBackwardPositionCases |
| R65 | EInfinity.Hammock.WordBackwardDecomposition |  禁止依存 25 本；EInfinity.Hammock.WordBackwardDecomposition → EInfinity.Hammock.WordBackwardBlockDirections |
| R65 | EInfinity.Hammock.WordDiagonalProper |  禁止依存 23 本；EInfinity.Hammock.WordDiagonalProper → EInfinity.Hammock.ProperDiagram |
| R65 | EInfinity.SimplicialLocalization.ComparisonEnrichedFunctors |  禁止依存 82 本；EInfinity.SimplicialLocalization.ComparisonEnrichedFunctors → EInfinity.SimplicialLocalization.ComparisonEnrichment |
| R65 | EInfinity.SimplicialLocalization.ComparisonEnrichment |  禁止依存 81 本；EInfinity.SimplicialLocalization.ComparisonEnrichment → EInfinity.SimplicialLocalization.Enrichment |
| R65 | EInfinity.SimplicialLocalization.ComponentCategory |  禁止依存 14 本；EInfinity.SimplicialLocalization.ComponentCategory → EInfinity.SimplicialLocalization.HomAugmentation |
| R65 | EInfinity.SimplicialLocalization.ComponentsEquivalence |  禁止依存 21 本；EInfinity.SimplicialLocalization.ComponentsEquivalence → EInfinity.SimplicialLocalization.ComponentsLocalizationLift |
| R65 | EInfinity.SimplicialLocalization.ComponentsLocalizationLift |  禁止依存 20 本；EInfinity.SimplicialLocalization.ComponentsLocalizationLift → EInfinity.SimplicialLocalization.ZeroLevelComponents |
| R65 | EInfinity.SimplicialLocalization.DKHammockCoefficientComparison |  禁止依存 499 本；EInfinity.SimplicialLocalization.DKHammockCoefficientComparison → EInfinity.Hammock.WeakAnodyneLocalization |
| R65 | EInfinity.SimplicialLocalization.DKHammockComponentsValue |  禁止依存 511 本；EInfinity.SimplicialLocalization.DKHammockComponentsValue → EInfinity.Hammock.AnodyneComponents |
| R65 | EInfinity.SimplicialLocalization.DKHammockCompositionComparison |  禁止依存 504 本；EInfinity.SimplicialLocalization.DKHammockCompositionComparison → EInfinity.Hammock.WeakTensor |
| R65 | EInfinity.SimplicialLocalization.DKHammockEndpointNaturality |  禁止依存 512 本；EInfinity.SimplicialLocalization.DKHammockEndpointNaturality → EInfinity.SimplicialLocalization.FreeHammockPrecompose |
| R65 | EInfinity.SimplicialLocalization.DKReducedHammockEndpointNaturality |  禁止依存 514 本；EInfinity.SimplicialLocalization.DKReducedHammockEndpointNaturality → EInfinity.Hammock.ReducedPointActions |
| R65 | EInfinity.SimplicialLocalization.EnrichedMap |  禁止依存 12 本；EInfinity.SimplicialLocalization.EnrichedMap → EInfinity.SimplicialLocalization.Enrichment |
| R65 | EInfinity.SimplicialLocalization.Enrichment |  禁止依存 7 本；EInfinity.SimplicialLocalization.Enrichment → EInfinity.SimplicialLocalization.Hom |
| R65 | EInfinity.SimplicialLocalization.FreeHammockArrowAugmentation |  禁止依存 81 本；EInfinity.SimplicialLocalization.FreeHammockArrowAugmentation → EInfinity.Hammock.RelativeFixedArrow |
| R65 | EInfinity.SimplicialLocalization.FreeHammockArrowPoint |  禁止依存 509 本；EInfinity.SimplicialLocalization.FreeHammockArrowPoint → EInfinity.SimplicialLocalization.DKHammockCompositionComparison |
| R65 | EInfinity.SimplicialLocalization.FreeHammockArrowZero |  禁止依存 78 本；EInfinity.SimplicialLocalization.FreeHammockArrowZero → EInfinity.Hammock.HammockValueForward |
| R65 | EInfinity.SimplicialLocalization.FreeHammockAugmentation |  禁止依存 19 本；EInfinity.SimplicialLocalization.FreeHammockAugmentation → EInfinity.SimplicialLocalization.FreeHammockDiagram |
| R65 | EInfinity.SimplicialLocalization.FreeHammockAugmentationValue |  禁止依存 77 本；EInfinity.SimplicialLocalization.FreeHammockAugmentationValue → EInfinity.Hammock.HammockValueComposition |
| R65 | EInfinity.SimplicialLocalization.FreeHammockComparison |  禁止依存 69 本；EInfinity.SimplicialLocalization.FreeHammockComparison → EInfinity.Hammock.FixedObjectLocalizationEvaluation |
| R65 | EInfinity.SimplicialLocalization.FreeHammockComparisonWeak |  禁止依存 246 本；EInfinity.SimplicialLocalization.FreeHammockComparisonWeak → EInfinity.Hammock.FixedObjectHomTransportIso |
| R65 | EInfinity.SimplicialLocalization.FreeHammockComposition |  禁止依存 76 本；EInfinity.SimplicialLocalization.FreeHammockComposition → EInfinity.Hammock.FixedObjectComposition |
| R65 | EInfinity.SimplicialLocalization.FreeHammockDiagonal |  禁止依存 62 本；EInfinity.SimplicialLocalization.FreeHammockDiagonal → EInfinity.Hammock.ReducedColimit |
| R65 | EInfinity.SimplicialLocalization.FreeHammockDiagonalComparisonWeak |  禁止依存 348 本；EInfinity.SimplicialLocalization.FreeHammockDiagonalComparisonWeak → EInfinity.Hammock.DoubleSimplicialWeak |
| R65 | EInfinity.SimplicialLocalization.FreeHammockDiagonalReductionWeak |  禁止依存 380 本；EInfinity.SimplicialLocalization.FreeHammockDiagonalReductionWeak → EInfinity.Hammock.WeakProperColimit |
| R65 | EInfinity.SimplicialLocalization.FreeHammockDiagram |  禁止依存 18 本；EInfinity.SimplicialLocalization.FreeHammockDiagram → EInfinity.SimplicialLocalization.FreeHammockObjects |
| R65 | EInfinity.SimplicialLocalization.FreeHammockGeneratorWords |  禁止依存 64 本；EInfinity.SimplicialLocalization.FreeHammockGeneratorWords → EInfinity.Hammock.UnmarkedGeneratorValue |
| R65 | EInfinity.SimplicialLocalization.FreeHammockLocalizedObjects |  禁止依存 64 本；EInfinity.SimplicialLocalization.FreeHammockLocalizedObjects → EInfinity.Hammock.FixedObjectLocalizationValue |
| R65 | EInfinity.SimplicialLocalization.FreeHammockMap |  禁止依存 64 本；EInfinity.SimplicialLocalization.FreeHammockMap → EInfinity.SimplicialLocalization.FreeHammockDiagonal |
| R65 | EInfinity.SimplicialLocalization.FreeHammockMapAugmentation |  禁止依存 66 本；EInfinity.SimplicialLocalization.FreeHammockMapAugmentation → EInfinity.Hammock.RelativeColimitMap |
| R65 | EInfinity.SimplicialLocalization.FreeHammockMapComparison |  禁止依存 72 本；EInfinity.SimplicialLocalization.FreeHammockMapComparison → EInfinity.SimplicialLocalization.EnrichedMap |
| R65 | EInfinity.SimplicialLocalization.FreeHammockObjectMap |  禁止依存 18 本；EInfinity.SimplicialLocalization.FreeHammockObjectMap → EInfinity.SimplicialLocalization.FreeHammockObjects |
| R65 | EInfinity.SimplicialLocalization.FreeHammockObjects |  禁止依存 17 本；EInfinity.SimplicialLocalization.FreeHammockObjects → EInfinity.SimplicialLocalization.ResolutionObjects |
| R65 | EInfinity.SimplicialLocalization.FreeHammockPostcompose |  禁止依存 510 本；EInfinity.SimplicialLocalization.FreeHammockPostcompose → EInfinity.SimplicialLocalization.FreeHammockArrowPoint |
| R65 | EInfinity.SimplicialLocalization.FreeHammockPrecompose |  禁止依存 511 本；EInfinity.SimplicialLocalization.FreeHammockPrecompose → EInfinity.SimplicialLocalization.FreeHammockPostcompose |
| R65 | EInfinity.SimplicialLocalization.FreeHammockUnit |  禁止依存 80 本；EInfinity.SimplicialLocalization.FreeHammockUnit → EInfinity.Hammock.HammockValueForward |
| R65 | EInfinity.SimplicialLocalization.FreeResolution |  禁止依存 3 本；EInfinity.SimplicialLocalization.FreeResolution → HA.HomotopyFunctionComplex.ComonadSimplicialResolution |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionCanonicalMarkedHom |  禁止依存 96 本；EInfinity.SimplicialLocalization.FreeResolutionCanonicalMarkedHom → EInfinity.Hammock.SingleZigzagHomDiagram |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionFunctoriality |  禁止依存 6 本；EInfinity.SimplicialLocalization.FreeResolutionFunctoriality → EInfinity.FrameHom.ComonadResolutionMap |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionGeneratorBlocks |  禁止依存 5 本；EInfinity.SimplicialLocalization.FreeResolutionGeneratorBlocks → EInfinity.SimplicialLocalization.FreeResolutionGeneratorPartition |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionGeneratorHom |  禁止依存 19 本；EInfinity.SimplicialLocalization.FreeResolutionGeneratorHom → EInfinity.SimplicialLocalization.FreeResolutionUnderlyingHom |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionGeneratorHomOperators |  禁止依存 20 本；EInfinity.SimplicialLocalization.FreeResolutionGeneratorHomOperators → EInfinity.SimplicialLocalization.FreeResolutionGeneratorHom |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionGeneratorPartition |  禁止依存 4 本；EInfinity.SimplicialLocalization.FreeResolutionGeneratorPartition → EInfinity.SimplicialLocalization.FreeResolution |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionHomContraction |  禁止依存 83 本；EInfinity.SimplicialLocalization.FreeResolutionHomContraction → EInfinity.FrameHom.AnodyneWeakDetection |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionHomExtra |  禁止依存 21 本；EInfinity.SimplicialLocalization.FreeResolutionHomExtra → EInfinity.SimplicialLocalization.FreeResolutionGeneratorHomOperators |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionHomExtraNaturality |  禁止依存 22 本；EInfinity.SimplicialLocalization.FreeResolutionHomExtraNaturality → EInfinity.SimplicialLocalization.FreeResolutionHomExtra |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionHomRepresentation |  禁止依存 84 本；EInfinity.SimplicialLocalization.FreeResolutionHomRepresentation → EInfinity.SimplicialLocalization.FreeResolutionHomContraction |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionMarkedHom |  禁止依存 85 本；EInfinity.SimplicialLocalization.FreeResolutionMarkedHom → EInfinity.SimplicialLocalization.FreeResolutionHomRepresentation |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionMarkedHomContraction |  禁止依存 86 本；EInfinity.SimplicialLocalization.FreeResolutionMarkedHomContraction → EInfinity.SimplicialLocalization.FreeResolutionMarkedHom |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionNativeMarkedHom |  禁止依存 87 本；EInfinity.SimplicialLocalization.FreeResolutionNativeMarkedHom → EInfinity.SimplicialLocalization.FreeResolutionMarkedHomContraction |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionNativeMarkedHomWeak |  禁止依存 88 本；EInfinity.SimplicialLocalization.FreeResolutionNativeMarkedHomWeak → EInfinity.SimplicialLocalization.FreeResolutionNativeMarkedHom |
| R65 | EInfinity.SimplicialLocalization.FreeResolutionUnderlyingHom |  禁止依存 18 本；EInfinity.SimplicialLocalization.FreeResolutionUnderlyingHom → EInfinity.SimplicialLocalization.FreeHammockObjects |
| R65 | EInfinity.SimplicialLocalization.FreeWordDiagonalBackwardWeak |  禁止依存 200 本；EInfinity.SimplicialLocalization.FreeWordDiagonalBackwardWeak → EInfinity.SimplicialLocalization.FreeResolutionCanonicalMarkedHom |
| R65 | EInfinity.SimplicialLocalization.FreeWordDiagonalEmptyWeak |  禁止依存 196 本；EInfinity.SimplicialLocalization.FreeWordDiagonalEmptyWeak → EInfinity.Hammock.EmptyWordDiagonalWeak |
| R65 | EInfinity.SimplicialLocalization.FreeWordDiagonalForwardWeak |  禁止依存 194 本；EInfinity.SimplicialLocalization.FreeWordDiagonalForwardWeak → EInfinity.Hammock.SingleZigzagDiagonalEvaluation |
| R65 | EInfinity.SimplicialLocalization.FreeWordDiagonalWeak |  禁止依存 336 本；EInfinity.SimplicialLocalization.FreeWordDiagonalWeak → EInfinity.Hammock.FreeFirstColumnBackwardStep |
| R65 | EInfinity.SimplicialLocalization.HammockInvertsEdges |  禁止依存 575 本；EInfinity.SimplicialLocalization.HammockInvertsEdges → EInfinity.SimplicialLocalization.KanHammockWeakArrows |
| R65 | EInfinity.SimplicialLocalization.HammockSourceFunctor |  禁止依存 82 本；EInfinity.SimplicialLocalization.HammockSourceFunctor → EInfinity.SimplicialLocalization.ComparisonEnrichment |
| R65 | EInfinity.SimplicialLocalization.Hom |  禁止依存 6 本；EInfinity.SimplicialLocalization.Hom → EInfinity.SimplicialLocalization.ResolutionObjects |
| R65 | EInfinity.SimplicialLocalization.HomAugmentation |  禁止依存 13 本；EInfinity.SimplicialLocalization.HomAugmentation → EInfinity.SimplicialLocalization.EnrichedMap |
| R65 | EInfinity.SimplicialLocalization.HomMapLaws |  禁止依存 13 本；EInfinity.SimplicialLocalization.HomMapLaws → EInfinity.SimplicialLocalization.EnrichedMap |
| R65 | EInfinity.SimplicialLocalization.KanComparisonEnrichedFunctors |  禁止依存 144 本；EInfinity.SimplicialLocalization.KanComparisonEnrichedFunctors → EInfinity.Hammock.ExInfinityEnrichedFunctor |
| R65 | EInfinity.SimplicialLocalization.KanComparisonNerves |  禁止依存 569 本；EInfinity.SimplicialLocalization.KanComparisonNerves → EInfinity.SimplicialLocalization.KanComparisonWeak |
| R65 | EInfinity.SimplicialLocalization.KanComparisonWeak |  禁止依存 567 本；EInfinity.SimplicialLocalization.KanComparisonWeak → EInfinity.Hammock.ExInfinityWeakMap |
| R65 | EInfinity.SimplicialLocalization.KanComponents |  禁止依存 97 本；EInfinity.SimplicialLocalization.KanComponents → EInfinity.SimplicialLocalization.ComponentsEquivalence |
| R65 | EInfinity.SimplicialLocalization.KanEnrichedMap |  禁止依存 87 本；EInfinity.SimplicialLocalization.KanEnrichedMap → EInfinity.SimplicialLocalization.EnrichedMap |
| R65 | EInfinity.SimplicialLocalization.KanEnrichment |  禁止依存 81 本；EInfinity.SimplicialLocalization.KanEnrichment → EInfinity.SimplicialLocalization.Enrichment |
| R65 | EInfinity.SimplicialLocalization.KanHammockArrowNormalization |  禁止依存 574 本；EInfinity.SimplicialLocalization.KanHammockArrowNormalization → EInfinity.SimplicialLocalization.KanHammockHomPinched |
| R65 | EInfinity.SimplicialLocalization.KanHammockHomCoherent |  禁止依存 786 本；EInfinity.SimplicialLocalization.KanHammockHomCoherent → EInfinity.FrameHom.EnrichedHomRealization |
| R65 | EInfinity.SimplicialLocalization.KanHammockHomInfinity |  禁止依存 788 本；EInfinity.SimplicialLocalization.KanHammockHomInfinity → EInfinity.FrameHom.EnrichedHomYoneda |
| R65 | EInfinity.SimplicialLocalization.KanHammockHomPinched |  禁止依存 573 本；EInfinity.SimplicialLocalization.KanHammockHomPinched → EInfinity.SimplicialLocalization.KanHammockSourceFunctor |
| R65 | EInfinity.SimplicialLocalization.KanHammockHomPinchedValue |  禁止依存 574 本；EInfinity.SimplicialLocalization.KanHammockHomPinchedValue → EInfinity.SimplicialLocalization.KanHammockHomPinched |
| R65 | EInfinity.SimplicialLocalization.KanHammockPrecompose |  禁止依存 573 本；EInfinity.SimplicialLocalization.KanHammockPrecompose → EInfinity.SimplicialLocalization.KanHammockSourceFunctor |
| R65 | EInfinity.SimplicialLocalization.KanHammockSourceFunctor |  禁止依存 572 本；EInfinity.SimplicialLocalization.KanHammockSourceFunctor → EInfinity.Hammock.ExInfinityEnrichedUnit |
| R65 | EInfinity.SimplicialLocalization.KanHammockWeakArrows |  禁止依存 574 本；EInfinity.SimplicialLocalization.KanHammockWeakArrows → EInfinity.Hammock.CoherentComponents |
| R65 | EInfinity.SimplicialLocalization.KanHammockYonedaNormalization |  禁止依存 791 本；EInfinity.SimplicialLocalization.KanHammockYonedaNormalization → EInfinity.SimplicialLocalization.KanHammockHomInfinity |
| R65 | EInfinity.SimplicialLocalization.KanMapLaws |  禁止依存 89 本；EInfinity.SimplicialLocalization.KanMapLaws → EInfinity.SimplicialLocalization.HomMapLaws |
| R65 | EInfinity.SimplicialLocalization.LocalizationNervePrecomposition |  禁止依存 577 本；EInfinity.SimplicialLocalization.LocalizationNervePrecomposition → EInfinity.SimplicialLocalization.LocalizationNerveSource |
| R65 | EInfinity.SimplicialLocalization.LocalizationNerveSource |  禁止依存 576 本；EInfinity.SimplicialLocalization.LocalizationNerveSource → EInfinity.SimplicialLocalization.HammockInvertsEdges |
| R65 | EInfinity.SimplicialLocalization.LocalizedFreeResolution |  禁止依存 4 本；EInfinity.SimplicialLocalization.LocalizedFreeResolution → EInfinity.SimplicialLocalization.FreeResolution |
| R65 | EInfinity.SimplicialLocalization.LocalizedResolutionFunctoriality |  禁止依存 9 本；EInfinity.SimplicialLocalization.LocalizedResolutionFunctoriality → EInfinity.SimplicialLocalization.FreeResolutionFunctoriality |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantFramePinchedWeak |  禁止依存 1295 本；EInfinity.SimplicialLocalization.ModelBifibrantFramePinchedWeak → EInfinity.SimplicialLocalization.ModelBifibrantRightKanShape → EInfinity.FrameHom.FrameRightKan → IC.Derived.CosliceInitialRealization |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantFrameRightKanCofinality |  禁止依存 2397 本；EInfinity.SimplicialLocalization.ModelBifibrantFrameRightKanCofinality → IC.Derived.RelativeRoofComparisonCofinality |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantFrameRoof |  禁止依存 1297 本；EInfinity.SimplicialLocalization.ModelBifibrantFrameRoof → EInfinity.FrameHom.FrameRoofSource → IC.Derived.RoofComparisonTransport |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantFrameRoofWeak |  禁止依存 3 本；EInfinity.SimplicialLocalization.ModelBifibrantFrameRoofWeak → EInfinity.FrameHom.FrameFunctorImage → EInfinity.FrameHom.FrameIndexAugmentation → EInfinity.FrameHom.SimplexTerminalEquivalence → EInfinity.FrameHom.SimplexTerminalStandard → EInfinity.FrameHom.SimplexTerminalFunctor → KST.ProExcision.NerveOppositeIso |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantLocalization |  禁止依存 2403 本；EInfinity.SimplicialLocalization.ModelBifibrantLocalization → EInfinity.SimplicialLocalization.ModelBifibrantFrameRightKanCofinality → IC.Derived.RelativeRoofComparisonCofinality |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantRightKanReduction |  禁止依存 1301 本；EInfinity.SimplicialLocalization.ModelBifibrantRightKanReduction → IC.Derived.CofinalLimitTransfer |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantRightKanShape |  禁止依存 1295 本；EInfinity.SimplicialLocalization.ModelBifibrantRightKanShape → EInfinity.FrameHom.FrameRightKan → IC.Derived.CosliceInitialRealization |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceFrameGraph |  禁止依存 1295 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceFrameGraph → EInfinity.SimplicialLocalization.ModelBifibrantFramePinchedWeak → EInfinity.SimplicialLocalization.ModelBifibrantRightKanShape → EInfinity.FrameHom.FrameRightKan → IC.Derived.CosliceInitialRealization |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofBaseEvaluation |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofBaseEvaluation → EInfinity.FrameHom.FrameRoofCornerLeftBase → EInfinity.FrameHom.TerminalFiberBaseHomotopy → IC.Derived.RoofTerminalEvaluation |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofCornerEvaluation |  禁止依存 1332 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofCornerEvaluation → EInfinity.FrameHom.FrameRoofCornerEvaluation → EInfinity.FrameHom.TerminalFiberEvaluationWeak → IC.Derived.RoofTerminalEvaluation |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofCornerOver |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofCornerOver → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofDegreeModel |  禁止依存 1299 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofDegreeModel → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSlices → EInfinity.FrameHom.FrameRoofQuillenSlice → EInfinity.FrameHom.FrameRoofTarget → IC.Derived.RoofLocallyConstantPullback |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofEvaluationHomotopy |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofEvaluationHomotopy → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell → EInfinity.FrameHom.FrameArrowAugmentationLimits → IC.Derived.WeaklyContractibleConstantLimit |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofGeometricLeftCell |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofGeometricLeftCell → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofEvaluationHomotopy → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell → EInfinity.FrameHom.FrameArrowAugmentationLimits → IC.Derived.WeaklyContractibleConstantLimit |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofGeometricRightCell |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofGeometricRightCell → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductGeometricTriangle → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePinchedReference |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePinchedReference → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrism |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrism → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeSimplex → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixPath → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePinchedReference → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismOne |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismOne → EInfinity.SimplicialLocalization.KanHammockHomPinchedValue → EInfinity.SimplicialLocalization.KanHammockHomPinched → EInfinity.SimplicialLocalization.KanHammockSourceFunctor → EInfinity.Hammock.ExInfinityEnrichedUnit → EInfinity.Hammock.ExInfinityEnrichedFunctor → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismProjection |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismProjection → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofEvaluationHomotopy → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell → EInfinity.FrameHom.FrameArrowAugmentationLimits → IC.Derived.WeaklyContractibleConstantLimit |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismZero |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismZero → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell → EInfinity.FrameHom.FrameArrowAugmentationLimits → IC.Derived.WeaklyContractibleConstantLimit |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeSimplex |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeSimplex → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixPath → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePinchedReference → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeTriangle |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeTriangle → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismZero → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell → EInfinity.FrameHom.FrameArrowAugmentationLimits → IC.Derived.WeaklyContractibleConstantLimit |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixHomotopy |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixHomotopy → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixNaturality |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixNaturality → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixHomotopy → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixPath |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixPath → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePinchedReference → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone |  禁止依存 2355 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell → EInfinity.FrameHom.FrameArrowAugmentationLimits → IC.Derived.WeaklyContractibleConstantLimit |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductGeometricTriangle |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductGeometricTriangle → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductIntervalCriterion |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductIntervalCriterion → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell → EInfinity.FrameHom.FrameArrowAugmentationLimits → IC.Derived.WeaklyContractibleConstantLimit |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductReference |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductReference → EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone → EInfinity.BarrattEccles.CofibrantSourceFrameLimits |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofRightSlice |  禁止依存 2388 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofRightSlice → EInfinity.FrameHom.FrameRoofSourceProjection → EInfinity.FrameHom.FrameRoofSource → IC.Derived.RoofComparisonTransport |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSliceCriterion |  禁止依存 1330 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSliceCriterion → EInfinity.FrameHom.FrameRoofSliceWeakContractibility → KST.Comparison.ArbitraryBasePullback |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSliceFibration |  禁止依存 1303 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSliceFibration → EInfinity.FrameHom.FrameRoofSliceFibration → EInfinity.FrameHom.PointSliceCornerFibration → IC.Derived.SliceRoofCorner |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSlices |  禁止依存 1299 本；EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSlices → EInfinity.FrameHom.FrameRoofQuillenSlice → EInfinity.FrameHom.FrameRoofTarget → IC.Derived.RoofLocallyConstantPullback |
| R65 | EInfinity.SimplicialLocalization.ModelBifibrantSpecifiedLocalization |  禁止依存 2415 本；EInfinity.SimplicialLocalization.ModelBifibrantSpecifiedLocalization → EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.SimplicialLocalization.ModelCofibrantRightKanShape |  禁止依存 1295 本；EInfinity.SimplicialLocalization.ModelCofibrantRightKanShape → EInfinity.FrameHom.FrameRightKan → IC.Derived.CosliceInitialRealization |
| R65 | EInfinity.SimplicialLocalization.ModelHammockLocalization |  禁止依存 2403 本；EInfinity.SimplicialLocalization.ModelHammockLocalization → EInfinity.SimplicialLocalization.ModelBifibrantLocalization → EInfinity.SimplicialLocalization.ModelBifibrantFrameRightKanCofinality → IC.Derived.RelativeRoofComparisonCofinality |
| R65 | EInfinity.SimplicialLocalization.ModelHammockNerveEquivalence |  禁止依存 62 本；EInfinity.SimplicialLocalization.ModelHammockNerveEquivalence → EInfinity.SimplicialLocalization.RelativeHammockNerveEquivalence → EInfinity.SimplicialLocalization.RelativeHammockEnriched → EInfinity.Hammock.ExInfinityWeakMap → KST.Comparison.ExInfinityMonoidal |
| R65 | EInfinity.SimplicialLocalization.ModelRightFrameComparison |  禁止依存 2415 本；EInfinity.SimplicialLocalization.ModelRightFrameComparison → EInfinity.FrameHom.RightFrameSpecifiedUnit → EInfinity.FrameHom.RightFrameSpecifiedLocalization → EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.SimplicialLocalization.ModelRightFrameSpecifiedInput |  禁止依存 2415 本；EInfinity.SimplicialLocalization.ModelRightFrameSpecifiedInput → EInfinity.FrameHom.RightFrameSpecifiedLocalization → EInfinity.FrameHom.LocalizationComparison → KST.LocalizingInvariants.LocalizationUniqueness |
| R65 | EInfinity.SimplicialLocalization.Nerve |  禁止依存 82 本；EInfinity.SimplicialLocalization.Nerve → EInfinity.SimplicialLocalization.KanEnrichment |
| R65 | EInfinity.SimplicialLocalization.NerveFunctor |  禁止依存 92 本；EInfinity.SimplicialLocalization.NerveFunctor → EInfinity.SimplicialLocalization.KanMapLaws |
| R65 | EInfinity.SimplicialLocalization.NerveMap |  禁止依存 89 本；EInfinity.SimplicialLocalization.NerveMap → EInfinity.SimplicialLocalization.KanEnrichedMap |
| R65 | EInfinity.SimplicialLocalization.NerveWeakVertexIso |  禁止依存 577 本；EInfinity.SimplicialLocalization.NerveWeakVertexIso → EInfinity.SimplicialLocalization.LocalizationNerveSource |
| R65 | EInfinity.SimplicialLocalization.RelativeHammockEnriched |  禁止依存 570 本；EInfinity.SimplicialLocalization.RelativeHammockEnriched → EInfinity.Hammock.ExInfinityWeakMap |
| R65 | EInfinity.SimplicialLocalization.RelativeHammockNerveEquivalence |  禁止依存 578 本；EInfinity.SimplicialLocalization.RelativeHammockNerveEquivalence → EInfinity.SimplicialLocalization.HammockInvertsEdges |
| R65 | EInfinity.SimplicialLocalization.RelativeHammockSourceComparison |  禁止依存 574 本；EInfinity.SimplicialLocalization.RelativeHammockSourceComparison → EInfinity.SimplicialLocalization.KanHammockSourceFunctor |
| R65 | EInfinity.SimplicialLocalization.ResolutionFaces |  禁止依存 17 本；EInfinity.SimplicialLocalization.ResolutionFaces → EInfinity.SimplicialLocalization.ResolutionRepresentatives |
| R65 | EInfinity.SimplicialLocalization.ResolutionGenerators |  禁止依存 15 本；EInfinity.SimplicialLocalization.ResolutionGenerators → EInfinity.SimplicialLocalization.ComponentCategory |
| R65 | EInfinity.SimplicialLocalization.ResolutionObjects |  禁止依存 5 本；EInfinity.SimplicialLocalization.ResolutionObjects → EInfinity.SimplicialLocalization.LocalizedFreeResolution |
| R65 | EInfinity.SimplicialLocalization.ResolutionRepresentatives |  禁止依存 16 本；EInfinity.SimplicialLocalization.ResolutionRepresentatives → EInfinity.SimplicialLocalization.ResolutionGenerators |
| R65 | EInfinity.SimplicialLocalization.ResolutionWordEdge |  禁止依存 18 本；EInfinity.SimplicialLocalization.ResolutionWordEdge → EInfinity.SimplicialLocalization.ResolutionFaces |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixColumnRoof |  禁止依存 2169 本；EInfinity.SimplicialLocalization.RoofPrefixColumnRoof → EInfinity.ComplexLimits.PinchedFamilyPostcompArrow |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixFamilyTriangle |  禁止依存 2164 本；EInfinity.SimplicialLocalization.RoofPrefixFamilyTriangle → EInfinity.FrameHom.FrameArrowAugmentationLimits |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPath |  禁止依存 587 本；EInfinity.SimplicialLocalization.RoofPrefixPath → EInfinity.Hammock.LeftRoofPrefixPath |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPathComposition |  禁止依存 589 本；EInfinity.SimplicialLocalization.RoofPrefixPathComposition → EInfinity.SimplicialLocalization.KanHammockPrecompose |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismCompatibility |  禁止依存 592 本；EInfinity.SimplicialLocalization.RoofPrefixPrismCompatibility → EInfinity.SimplicialLocalization.RoofPrefixPrismLast |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismFront |  禁止依存 590 本；EInfinity.SimplicialLocalization.RoofPrefixPrismFront → EInfinity.SimplicialLocalization.RoofPrefixPathComposition |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismLast |  禁止依存 591 本；EInfinity.SimplicialLocalization.RoofPrefixPrismLast → EInfinity.SimplicialLocalization.RoofPrefixPrismFront |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismNaturality |  禁止依存 595 本；EInfinity.SimplicialLocalization.RoofPrefixPrismNaturality → EInfinity.SimplicialLocalization.RoofPrefixPrismReindex |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismOne |  禁止依存 594 本；EInfinity.SimplicialLocalization.RoofPrefixPrismOne → EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismProjection |  禁止依存 596 本；EInfinity.SimplicialLocalization.RoofPrefixPrismProjection → EInfinity.SimplicialLocalization.RoofPrefixPrismNaturality |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismReindex |  禁止依存 592 本；EInfinity.SimplicialLocalization.RoofPrefixPrismReindex → EInfinity.SimplicialLocalization.RoofPrefixPrismLast |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex |  禁止依存 593 本；EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex → EInfinity.SimplicialLocalization.RoofPrefixPrismCompatibility |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismZero |  禁止依存 594 本；EInfinity.SimplicialLocalization.RoofPrefixPrismZero → EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex |
| R65 | EInfinity.SimplicialLocalization.RoofPrefixPrismZeroSlice |  禁止依存 597 本；EInfinity.SimplicialLocalization.RoofPrefixPrismZeroSlice → EInfinity.SimplicialLocalization.RoofPrefixPrismNaturality |
| R65 | EInfinity.SimplicialLocalization.WeakNerveInverts |  禁止依存 576 本；EInfinity.SimplicialLocalization.WeakNerveInverts → EInfinity.SimplicialLocalization.HammockInvertsEdges |
| R65 | EInfinity.SimplicialLocalization.ZeroLevelComponents |  禁止依存 19 本；EInfinity.SimplicialLocalization.ZeroLevelComponents → EInfinity.SimplicialLocalization.ResolutionWordEdge |
| R64 | HA.Simplicial.AnodyneHomotopyLocalization |  禁止依存 17 本；HA.Simplicial.AnodyneHomotopyLocalization → HA.Simplicial.AnodyneIntervalEndpoints |
| R64 | HA.Simplicial.AnodyneIntervalEndpoints |  禁止依存 16 本；HA.Simplicial.AnodyneIntervalEndpoints → HA.Simplicial.FixedBoundaryExtensions |
| R64 | HA.Simplicial.AnodyneKanReplacement |  禁止依存 12 本；HA.Simplicial.AnodyneKanReplacement → HA.Simplicial.Generators |
| R64 | HA.Simplicial.AnodyneLocalizedTensor |  禁止依存 18 本；HA.Simplicial.AnodyneLocalizedTensor → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | HA.Simplicial.AnodyneModelDetection |  禁止依存 20 本；HA.Simplicial.AnodyneModelDetection → HA.Quillen.Saturation |
| R64 | HA.Simplicial.AnodyneNonempty |  禁止依存 29 本；HA.Simplicial.AnodyneNonempty → HA.Simplicial.KanTestDetection |
| R64 | HA.Simplicial.BarAugmentation |  禁止依存 75 本；HA.Simplicial.BarAugmentation → HA.Simplicial.BarConstruction |
| R64 | HA.Simplicial.BarConstruction |  禁止依存 74 本；HA.Simplicial.BarConstruction → HA.Simplicial.DiagonalAdjunction |
| R64 | HA.Simplicial.BinaryCotensor |  禁止依存 18 本；HA.Simplicial.BinaryCotensor → HA.Simplicial.BoundaryCotensor |
| R64 | HA.Simplicial.BinaryIntervalEndpoints |  禁止依存 27 本；HA.Simplicial.BinaryIntervalEndpoints → HA.Simplicial.HomotopyBinarySquare |
| R64 | HA.Simplicial.BoundaryCotensor |  禁止依存 16 本；HA.Simplicial.BoundaryCotensor → HA.Simplicial.FixedBoundaryExtensions |
| R64 | HA.Simplicial.BoundaryFillerLifting |  禁止依存 20 本；HA.Simplicial.BoundaryFillerLifting → HA.Simplicial.LargeParameterExtension |
| R64 | HA.Simplicial.BoundaryOneCotensor |  禁止依存 16 本；HA.Simplicial.BoundaryOneCotensor → HA.Simplicial.FixedBoundaryExtensions |
| R64 | HA.Simplicial.BoundaryReedyFactorization |  禁止依存 90 本；HA.Simplicial.BoundaryReedyFactorization → HA.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem |
| R64 | HA.Simplicial.BoundaryRightColimit |  禁止依存 42 本；HA.Simplicial.BoundaryRightColimit → HA.Simplicial.Generators |
| R64 | HA.Simplicial.BoundaryTensorGluing |  禁止依存 17 本；HA.Simplicial.BoundaryTensorGluing → HA.Simplicial.BoundaryCotensor |
| R64 | HA.Simplicial.CellularNaturalComparison |  禁止依存 91 本；HA.Simplicial.CellularNaturalComparison → HA.Simplicial.KanLocalizedCoproducts |
| R64 | HA.Simplicial.ClosedHomotopyComposition |  禁止依存 24 本；HA.Simplicial.ClosedHomotopyComposition → HA.Simplicial.ClosedParameterComposition |
| R64 | HA.Simplicial.ClosedParameterComposition |  禁止依存 3 本；HA.Simplicial.ClosedParameterComposition → HA.Simplicial.ParameterComposition |
| R64 | HA.Simplicial.ClosedParameterUnits |  禁止依存 33 本；HA.Simplicial.ClosedParameterUnits → HA.Simplicial.BinaryIntervalEndpoints |
| R64 | HA.Simplicial.CurriedHomotopy |  禁止依存 21 本；HA.Simplicial.CurriedHomotopy → HA.Simplicial.LargeParameterHomotopy |
| R64 | HA.Simplicial.DiagonalAdjunction |  禁止依存 73 本；HA.Simplicial.DiagonalAdjunction → HA.HomotopyFunctionComplex.DiagonalFrame |
| R64 | HA.Simplicial.DiagonalAnodyne |  禁止依存 123 本；HA.Simplicial.DiagonalAnodyne → HA.HomotopyFunctionComplex.Reedy.Lifting |
| R64 | HA.Simplicial.DiagonalCofibrations |  禁止依存 81 本；HA.Simplicial.DiagonalCofibrations → HA.HomotopyFunctionComplex.Reedy.ComponentClasses |
| R64 | HA.Simplicial.DiagonalInternalHom |  禁止依存 101 本；HA.Simplicial.DiagonalInternalHom → HA.HomotopyFunctionComplex.AdjunctionHom |
| R64 | HA.Simplicial.DiagonalKanTests |  禁止依存 150 本；HA.Simplicial.DiagonalKanTests → HA.Simplicial.DiagonalAnodyne |
| R64 | HA.Simplicial.DiagonalLocalizedEquivalence |  禁止依存 170 本；HA.Simplicial.DiagonalLocalizedEquivalence → HA.Simplicial.BoundaryReedyFactorization |
| R64 | HA.Simplicial.DiagonalMatching |  禁止依存 104 本；HA.Simplicial.DiagonalMatching → HA.HomotopyFunctionComplex.Reedy.BoundaryHom |
| R64 | HA.Simplicial.DiagonalQuillen |  禁止依存 123 本；HA.Simplicial.DiagonalQuillen → HA.Simplicial.DiagonalCofibrations |
| R64 | HA.Simplicial.DiagonalRelativeMatching |  禁止依存 105 本；HA.Simplicial.DiagonalRelativeMatching → HA.Simplicial.DiagonalMatching |
| R64 | HA.Simplicial.DiagonalRepresentables |  禁止依存 74 本；HA.Simplicial.DiagonalRepresentables → HA.Simplicial.DiagonalAdjunction |
| R64 | HA.Simplicial.DiscreteFamilyLifting |  禁止依存 28 本；HA.Simplicial.DiscreteFamilyLifting → HA.Simplicial.MonoRightLiftingContraction |
| R64 | HA.Simplicial.DiscreteKanExtension |  禁止依存 30 本；HA.Simplicial.DiscreteKanExtension → HA.Simplicial.PiZeroLocalization |
| R64 | HA.Simplicial.DiscreteLocalizedExtension |  禁止依存 31 本；HA.Simplicial.DiscreteLocalizedExtension → HA.Simplicial.DiscreteKanExtension |
| R64 | HA.Simplicial.ExtraDegeneracyContraction |  禁止依存 22 本；HA.Simplicial.ExtraDegeneracyContraction → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | HA.Simplicial.ExtraDegeneracyInterval |  禁止依存 3 本；HA.Simplicial.ExtraDegeneracyInterval → CategoryTheory.Simplex.Naturality |
| R64 | HA.Simplicial.HomotopyBinarySquare |  禁止依存 19 本；HA.Simplicial.HomotopyBinarySquare → HA.Simplicial.HomotopyClasses |
| R64 | HA.Simplicial.HomotopyClasses | 衝突：HA.Simplicial.HomotopyClasses, IC.F1B.KanComplex.HomotopyClasses |
| R64 | HA.Simplicial.HomotopyClassesClosed |  禁止依存 19 本；HA.Simplicial.HomotopyClassesClosed → HA.Simplicial.HomotopyClasses |
| R64 | HA.Simplicial.HomotopyFaces |  禁止依存 21 本；HA.Simplicial.HomotopyFaces → HA.Simplicial.LargeParameterHomotopy |
| R64 | HA.Simplicial.HomotopyRetractionTests |  禁止依存 20 本；HA.Simplicial.HomotopyRetractionTests → HA.Simplicial.HomotopyClassesClosed |
| R64 | HA.Simplicial.KanActualHomotopy |  禁止依存 25 本；HA.Simplicial.KanActualHomotopy → HA.Simplicial.CurriedHomotopy |
| R64 | HA.Simplicial.KanFiberwiseContraction |  禁止依存 25 本；HA.Simplicial.KanFiberwiseContraction → HA.Simplicial.CurriedHomotopy |
| R64 | HA.Simplicial.KanFibrationEndpointExtension |  禁止依存 27 本；HA.Simplicial.KanFibrationEndpointExtension → HA.Simplicial.KanMonoEndpointExtension |
| R64 | HA.Simplicial.KanFibrationLocalizedLifting |  禁止依存 35 本；HA.Simplicial.KanFibrationLocalizedLifting → HA.Simplicial.KanActualHomotopy |
| R64 | HA.Simplicial.KanHomotopyClasses |  禁止依存 26 本；HA.Simplicial.KanHomotopyClasses → HA.Simplicial.KanHomotopyExtension |
| R64 | HA.Simplicial.KanHomotopyExtension |  禁止依存 25 本；HA.Simplicial.KanHomotopyExtension → HA.Simplicial.HomotopyClasses |
| R64 | HA.Simplicial.KanLocalizedCoproducts |  禁止依存 44 本；HA.Simplicial.KanLocalizedCoproducts → HA.Simplicial.KanTestLiftingClass |
| R64 | HA.Simplicial.KanLocalizedLeftProper |  禁止依存 54 本；HA.Simplicial.KanLocalizedLeftProper → HA.Simplicial.KanMonoPushoutEquivalence |
| R64 | HA.Simplicial.KanLocalizedMonoLifting |  禁止依存 42 本；HA.Simplicial.KanLocalizedMonoLifting → HA.Simplicial.KanFibrationEndpointExtension |
| R64 | HA.Simplicial.KanLocalizedRepresentatives |  禁止依存 29 本；HA.Simplicial.KanLocalizedRepresentatives → HA.Simplicial.KanActualHomotopy |
| R64 | HA.Simplicial.KanLocalizedTransfinite |  禁止依存 42 本；HA.Simplicial.KanLocalizedTransfinite → HA.Simplicial.KanTestLiftingClass |
| R64 | HA.Simplicial.KanMonoEndpointExtension |  禁止依存 26 本；HA.Simplicial.KanMonoEndpointExtension → HA.Simplicial.KanHomotopyExtension |
| R64 | HA.Simplicial.KanMonoPushoutEquivalence |  禁止依存 43 本；HA.Simplicial.KanMonoPushoutEquivalence → HA.Simplicial.KanMonoPushoutExtension |
| R64 | HA.Simplicial.KanMonoPushoutExtension |  禁止依存 31 本；HA.Simplicial.KanMonoPushoutExtension → HA.Simplicial.KanMonoStrictExtension |
| R64 | HA.Simplicial.KanMonoRelativeHomotopy |  禁止依存 40 本；HA.Simplicial.KanMonoRelativeHomotopy → HA.Simplicial.KanRelativeLifting |
| R64 | HA.Simplicial.KanMonoStrictExtension |  禁止依存 30 本；HA.Simplicial.KanMonoStrictExtension → HA.Simplicial.KanMonoEndpointExtension |
| R64 | HA.Simplicial.KanPostDetection |  禁止依存 26 本；HA.Simplicial.KanPostDetection → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | HA.Simplicial.KanPullbackDeformation |  禁止依存 30 本；HA.Simplicial.KanPullbackDeformation → HA.Simplicial.KanActualHomotopy |
| R64 | HA.Simplicial.KanPushoutComparison |  禁止依存 47 本；HA.Simplicial.KanPushoutComparison → HA.Simplicial.KanMonoPushoutEquivalence |
| R64 | HA.Simplicial.KanPushoutCube |  禁止依存 57 本；HA.Simplicial.KanPushoutCube → HA.Simplicial.KanLocalizedLeftProper |
| R64 | HA.Simplicial.KanRelativeLifting |  禁止依存 26 本；HA.Simplicial.KanRelativeLifting → HA.Simplicial.KanHomotopyExtension |
| R64 | HA.Simplicial.KanReplacement |  禁止依存 89 本；HA.Simplicial.KanReplacement → HA.HomotopyFunctionComplex.ChosenResolutionHom |
| R64 | HA.Simplicial.KanRestrictionEquivalence |  禁止依存 42 本；HA.Simplicial.KanRestrictionEquivalence → HA.Simplicial.KanPostDetection |
| R64 | HA.Simplicial.KanRestrictionLifting |  禁止依存 38 本；HA.Simplicial.KanRestrictionLifting → HA.Simplicial.AnodyneLocalizedTensor |
| R64 | HA.Simplicial.KanRetractionRightLifting |  禁止依存 30 本；HA.Simplicial.KanRetractionRightLifting → HA.Simplicial.KanFiberwiseContraction |
| R64 | HA.Simplicial.KanSequentialColimitComparison |  禁止依存 86 本；HA.Simplicial.KanSequentialColimitComparison → HA.Diagram.ColimitWeakEquivalence |
| R64 | HA.Simplicial.KanTestDetection |  禁止依存 28 本；HA.Simplicial.KanTestDetection → HA.Simplicial.AnodyneKanReplacement |
| R64 | HA.Simplicial.KanTestLiftingClass |  禁止依存 41 本；HA.Simplicial.KanTestLiftingClass → HA.Simplicial.KanMonoStrictExtension |
| R64 | HA.Simplicial.LargeParameterHomotopy |  禁止依存 20 本；HA.Simplicial.LargeParameterHomotopy → HA.Simplicial.LargeParameterExtension |
| R64 | HA.Simplicial.LargeParameterMapping |  禁止依存 21 本；HA.Simplicial.LargeParameterMapping → HA.Simplicial.LargeParameterHomotopy |
| R64 | HA.Simplicial.LatchingDegeneracies |  禁止依存 5 本；HA.Simplicial.LatchingDegeneracies → HA.HomotopyFunctionComplex.Reedy.SimplexFinite |
| R64 | HA.Simplicial.LatchingMonomorphisms |  禁止依存 6 本；HA.Simplicial.LatchingMonomorphisms → HA.Simplicial.LatchingDegeneracies |
| R64 | HA.Simplicial.LocalizedMonoReedy |  禁止依存 83 本；HA.Simplicial.LocalizedMonoReedy → HA.HomotopyFunctionComplex.Reedy.ClosedObjectwise |
| R64 | HA.Simplicial.MappingPrecompositionRetraction |  禁止依存 32 本；HA.Simplicial.MappingPrecompositionRetraction → HA.Simplicial.KanPullbackDeformation |
| R64 | HA.Simplicial.ModelCompatibility |  禁止依存 12 本；HA.Simplicial.ModelCompatibility → HA.Monoidal.ModelCategory |
| R64 | HA.Simplicial.MonoLocalizedFactorization |  禁止依存 28 本；HA.Simplicial.MonoLocalizedFactorization → HA.Simplicial.Generators |
| R64 | HA.Simplicial.MonoRightLiftingContraction |  禁止依存 27 本；HA.Simplicial.MonoRightLiftingContraction → HA.Simplicial.KanRelativeLifting |
| R64 | HA.Simplicial.MonoRightLiftingRelativeHomotopy |  禁止依存 28 本；HA.Simplicial.MonoRightLiftingRelativeHomotopy → HA.Simplicial.MonoRightLiftingContraction |
| R64 | HA.Simplicial.MonoRightPushoutEquivalence |  禁止依存 43 本；HA.Simplicial.MonoRightPushoutEquivalence → HA.Simplicial.HomotopyRetractionTests |
| R64 | HA.Simplicial.NerveInitialContraction |  禁止依存 19 本；HA.Simplicial.NerveInitialContraction → CategoryTheory.NerveHomotopy |
| R64 | HA.Simplicial.OppositeHomotopy |  禁止依存 23 本；HA.Simplicial.OppositeHomotopy → HA.Simplicial.ExtraDegeneracyContraction |
| R64 | HA.Simplicial.ParameterCategory |  禁止依存 3 本；HA.Simplicial.ParameterCategory → HA.Simplicial.ParameterComposition |
| R64 | HA.Simplicial.ParameterComposition |  禁止依存 2 本；HA.Simplicial.ParameterComposition → HA.Simplicial.SimplexParameterHom |
| R64 | HA.Simplicial.PiZeroLocalization |  禁止依存 29 本；HA.Simplicial.PiZeroLocalization → HA.Simplicial.KanTestDetection |
| R64 | HA.Simplicial.PiZeroWeakEquivalence |  禁止依存 1 本；HA.Simplicial.PiZeroWeakEquivalence → HA.HomotopyFunctionComplex.BoundaryOne |
| R64 | HA.Simplicial.PrecompositionHomotopy |  禁止依存 25 本；HA.Simplicial.PrecompositionHomotopy → HA.Simplicial.CurriedHomotopy |
| R64 | HA.Simplicial.ProductBoundaryCotensor |  禁止依存 17 本；HA.Simplicial.ProductBoundaryCotensor → HA.Simplicial.BoundaryCotensor |
| R64 | HA.Simplicial.PushoutCotensor |  禁止依存 17 本；HA.Simplicial.PushoutCotensor → HA.Simplicial.BoundaryCotensor |
| R64 | HA.Simplicial.PushoutInternalHomPullback |  禁止依存 18 本；HA.Simplicial.PushoutInternalHomPullback → HA.Simplicial.PushoutCotensor |
| R64 | HA.Simplicial.RelativeBarAnodyneComparison |  禁止依存 102 本；HA.Simplicial.RelativeBarAnodyneComparison → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | HA.Simplicial.RelativeBarAugmentation |  禁止依存 76 本；HA.Simplicial.RelativeBarAugmentation → HA.Simplicial.RelativeBarConstruction |
| R64 | HA.Simplicial.RelativeBarCommaPresentation |  禁止依存 79 本；HA.Simplicial.RelativeBarCommaPresentation → HA.Simplicial.RelativeBarConstruction |
| R64 | HA.Simplicial.RelativeBarConstruction |  禁止依存 75 本；HA.Simplicial.RelativeBarConstruction → HA.Simplicial.BarConstruction |
| R64 | HA.Simplicial.RelativeBarContractionOperators |  禁止依存 80 本；HA.Simplicial.RelativeBarContractionOperators → HA.Simplicial.RelativeBarIdentity |
| R64 | HA.Simplicial.RelativeBarDiagonalContraction |  禁止依存 81 本；HA.Simplicial.RelativeBarDiagonalContraction → HA.Simplicial.RelativeBarContractionOperators |
| R64 | HA.Simplicial.RelativeBarIdentity |  禁止依存 79 本；HA.Simplicial.RelativeBarIdentity → CategoryTheory.NerveHomotopy |
| R64 | HA.Simplicial.RelativeBarMiddleReindex |  禁止依存 104 本；HA.Simplicial.RelativeBarMiddleReindex → HA.Simplicial.RelativeBarAnodyneComparison |
| R64 | HA.Simplicial.RelativeBarReindex |  禁止依存 76 本；HA.Simplicial.RelativeBarReindex → HA.Simplicial.RelativeBarConstruction |
| R64 | HA.Simplicial.RelativeBarSectionHomotopy |  禁止依存 95 本；HA.Simplicial.RelativeBarSectionHomotopy → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | HA.Simplicial.RelativeBarSectionUnit |  禁止依存 105 本；HA.Simplicial.RelativeBarSectionUnit → HA.Simplicial.RelativeBarAnodyneComparison |
| R64 | HA.Simplicial.RelativeBarSections |  禁止依存 76 本；HA.Simplicial.RelativeBarSections → HA.Simplicial.RelativeBarConstruction |
| R64 | HA.Simplicial.RelativeBarSpan |  禁止依存 80 本；HA.Simplicial.RelativeBarSpan → HA.Simplicial.RelativeBarIdentity |
| R64 | HA.Simplicial.RelativeBarSpanContraction |  禁止依存 83 本；HA.Simplicial.RelativeBarSpanContraction → HA.Simplicial.RelativeBarDiagonalContraction |
| R64 | HA.Simplicial.RelativeBarUnit |  禁止依存 77 本；HA.Simplicial.RelativeBarUnit → HA.Simplicial.RelativeBarAugmentation |
| R64 | HA.Simplicial.RelativeProductLifting |  禁止依存 31 本；HA.Simplicial.RelativeProductLifting → HA.Simplicial.BoundaryTensorGluing |
| R64 | HA.Simplicial.SequentialBoundaryFactorization |  禁止依存 29 本；HA.Simplicial.SequentialBoundaryFactorization → HA.Simplicial.MonoLocalizedFactorization |
| R64 | HA.Simplicial.SequentialFactorLift |  禁止依存 58 本；HA.Simplicial.SequentialFactorLift → HA.Simplicial.SequentialFactorLiftingClasses |
| R64 | HA.Simplicial.SequentialFactorLiftingClasses |  禁止依存 57 本；HA.Simplicial.SequentialFactorLiftingClasses → HA.Simplicial.KanLocalizedLeftProper |
| R64 | HA.Simplicial.SimplexIndexFinite |  禁止依存 7 本；HA.Simplicial.SimplexIndexFinite → HA.HomotopyFunctionComplex.Reedy.ElementsFinite |
| R64 | HA.Simplicial.SimplexInverseMatching |  禁止依存 111 本；HA.Simplicial.SimplexInverseMatching → HA.Simplicial.SimplexLatchingBoundary |
| R64 | HA.Simplicial.SimplexLatchingBoundary |  禁止依存 109 本；HA.Simplicial.SimplexLatchingBoundary → HA.HomotopyFunctionComplex.Reedy.CofibrantBoundary |
| R64 | HA.Simplicial.SimplexMatchingTerminal |  禁止依存 8 本；HA.Simplicial.SimplexMatchingTerminal → HA.Simplicial.SimplexIndexFinite |
| R64 | HA.Simplicial.SimplexMonomorphismLifting |  禁止依存 113 本；HA.Simplicial.SimplexMonomorphismLifting → HA.Simplicial.SimplexNaturalMatching |
| R64 | HA.Simplicial.SimplexNaturalMatching |  禁止依存 112 本；HA.Simplicial.SimplexNaturalMatching → HA.Simplicial.SimplexInverseMatching |
| R64 | HA.Simplicial.SimplexNerveAugmentation |  禁止依存 1 本；HA.Simplicial.SimplexNerveAugmentation → CategoryTheory.SimplexChainVertices |
| R64 | HA.Simplicial.SimplexNerveEquivalence |  禁止依存 100 本；HA.Simplicial.SimplexNerveEquivalence → HA.Simplicial.CellularNaturalComparison |
| R64 | HA.Simplicial.SimplexNerveFunctor |  禁止依存 3 本；HA.Simplicial.SimplexNerveFunctor → CategoryTheory.ElementsChainLifting |
| R64 | HA.Simplicial.SimplexNerveMonos |  禁止依存 4 本；HA.Simplicial.SimplexNerveMonos → HA.Simplicial.SimplexNerveFunctor |
| R64 | HA.Simplicial.SimplexNerveStandard |  禁止依存 25 本；HA.Simplicial.SimplexNerveStandard → HA.Simplicial.NerveInitialContraction |
| R64 | HA.Simplicial.SimplexParameterHom |  禁止依存 1 本；HA.Simplicial.SimplexParameterHom → HA.HomotopyFunctionComplex.ResolutionHom |
| R64 | HA.Simplicial.SkeletalCellGluing |  禁止依存 1 本；HA.Simplicial.SkeletalCellGluing → CategoryTheory.Limits.SequentialExtension |
| R64 | HA.Simplicial.SmallDominatedSubcomplex |  禁止依存 18 本；HA.Simplicial.SmallDominatedSubcomplex → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | HA.Simplicial.SplitLocalizedDescent |  禁止依存 31 本；HA.Simplicial.SplitLocalizedDescent → HA.Simplicial.AnodyneLocalizedTensor |
| R64 | HA.Simplicial.StandardSimplexWeakEquivalence |  禁止依存 3 本；HA.Simplicial.StandardSimplexWeakEquivalence → HA.Simplicial.WeakEquivalence |
| R64 | HA.Simplicial.TotalNerveBarAugmentation |  禁止依存 77 本；HA.Simplicial.TotalNerveBarAugmentation → CategoryTheory.ElementsChainLifting |
| R64 | HA.Simplicial.UnderMonoBrown |  禁止依存 29 本；HA.Simplicial.UnderMonoBrown → HA.Simplicial.MonoLocalizedFactorization |
| R64 | HA.Simplicial.UniverseLiftAnodyneReflection |  禁止依存 36 本；HA.Simplicial.UniverseLiftAnodyneReflection → HA.Simplicial.KanHomotopyClasses |
| R64 | HA.Simplicial.UniverseLiftClosedComposition |  禁止依存 6 本；HA.Simplicial.UniverseLiftClosedComposition → HA.Simplicial.ClosedParameterComposition |
| R64 | HA.Simplicial.UniverseLiftClosedCurry |  禁止依存 3 本；HA.Simplicial.UniverseLiftClosedCurry → HA.Simplicial.UniverseLiftParameterHom |
| R64 | HA.Simplicial.UniverseLiftHomotopyClasses |  禁止依存 27 本；HA.Simplicial.UniverseLiftHomotopyClasses → HA.Simplicial.HomotopyClasses |
| R64 | HA.Simplicial.UniverseLiftLifting |  禁止依存 1 本；HA.Simplicial.UniverseLiftLifting → HA.Transfer.FullyFaithfulLifting |
| R64 | HA.Simplicial.UniverseLiftLocalizedHom |  禁止依存 40 本；HA.Simplicial.UniverseLiftLocalizedHom → HA.Simplicial.KanLocalizedRepresentatives |
| R64 | HA.Simplicial.UniverseLiftModel |  禁止依存 16 本；HA.Simplicial.UniverseLiftModel → HA.Quillen.FullyFaithfulReflection |
| R64 | HA.Simplicial.UniverseLiftParameterHom |  禁止依存 2 本；HA.Simplicial.UniverseLiftParameterHom → HA.Simplicial.SimplexParameterHom |
| R64 | HA.Simplicial.UniverseLiftWeakEquivalence |  禁止依存 17 本；HA.Simplicial.UniverseLiftWeakEquivalence → HA.Simplicial.UniverseLiftModel |
| R64 | HA.Simplicial.WeakEquivalence |  禁止依存 1 本；HA.Simplicial.WeakEquivalence → HA.Topological.WeakEquivalence |
| R64 | IC.F1.KanModels.KanAnodyneLocalization |  禁止依存 33 本；IC.F1.KanModels.KanAnodyneLocalization → HA.Simplicial.KanTestDetection |
| R64 | IC.F1.KanModels.KanEdgewiseFunctor |  禁止依存 589 本；IC.F1.KanModels.KanEdgewiseFunctor → IC.F1.KanModels.KanOppositeCoefficients |
| R64 | IC.F1.KanModels.KanEnrichedComparison |  禁止依存 418 本；IC.F1.KanModels.KanEnrichedComparison → IC.F1.Categories.KanDiagramEvaluation |
| R64 | IC.F1.KanModels.KanEnrichedComparisonArrow |  禁止依存 419 本；IC.F1.KanModels.KanEnrichedComparisonArrow → IC.F1.KanModels.KanEnrichedComparison |
| R64 | IC.F1.KanModels.KanEnrichedComparisonComposition |  禁止依存 679 本；IC.F1.KanModels.KanEnrichedComparisonComposition → IC.F1.KanModels.KanEnrichedComparisonIso |
| R64 | IC.F1.KanModels.KanEnrichedComparisonEdgeComposition |  禁止依存 684 本；IC.F1.KanModels.KanEnrichedComparisonEdgeComposition → IC.F1.KanModels.KanEnrichedComparisonIndexTriangle |
| R64 | IC.F1.KanModels.KanEnrichedComparisonFaces |  禁止依存 682 本；IC.F1.KanModels.KanEnrichedComparisonFaces → IC.F1.KanModels.KanEnrichedComparisonTriangle |
| R64 | IC.F1.KanModels.KanEnrichedComparisonIndexTriangle |  禁止依存 683 本；IC.F1.KanModels.KanEnrichedComparisonIndexTriangle → IC.F1.KanModels.KanEnrichedComparisonFaces |
| R64 | IC.F1.KanModels.KanEnrichedComparisonIso |  禁止依存 678 本；IC.F1.KanModels.KanEnrichedComparisonIso → IC.F1.Coherent.ResolutionComparisonEdge |
| R64 | IC.F1.KanModels.KanEnrichedComparisonTriangle |  禁止依存 681 本；IC.F1.KanModels.KanEnrichedComparisonTriangle → IC.F1.KanModels.KanEnrichedComparisonComposition |
| R64 | IC.F1.KanModels.KanEnrichedDiagram |  禁止依存 679 本；IC.F1.KanModels.KanEnrichedDiagram → IC.F1.KanModels.KanEnrichedComparisonIso |
| R64 | IC.F1.KanModels.KanEnrichedDiagramArrow |  禁止依存 686 本；IC.F1.KanModels.KanEnrichedDiagramArrow → IC.F1.Diagrams.RelativeSectionDiagram |
| R64 | IC.F1.KanModels.KanEnrichedDiagramComparison |  禁止依存 684 本；IC.F1.KanModels.KanEnrichedDiagramComparison → IC.F1.Diagrams.StrictDiagramPostcomposition |
| R64 | IC.F1.KanModels.KanEnrichedDiagramDiagonalComparison |  禁止依存 685 本；IC.F1.KanModels.KanEnrichedDiagramDiagonalComparison → IC.F1.KanModels.KanEnrichedDiagramComparison |
| R64 | IC.F1.KanModels.KanEnrichedDiagramEdges |  禁止依存 680 本；IC.F1.KanModels.KanEnrichedDiagramEdges → IC.F1.KanModels.KanEnrichedDiagram |
| R64 | IC.F1.KanModels.KanEnrichedDiagramEdgewise |  禁止依存 742 本；IC.F1.KanModels.KanEnrichedDiagramEdgewise → IC.F1.KanModels.KanEnrichedDiagramJointComparison |
| R64 | IC.F1.KanModels.KanEnrichedDiagramHomIntervalCriterion |  禁止依存 765 本；IC.F1.KanModels.KanEnrichedDiagramHomIntervalCriterion → IC.F1.Coherent.HomEquivalence |
| R64 | IC.F1.KanModels.KanEnrichedDiagramJointComparison |  禁止依存 695 本；IC.F1.KanModels.KanEnrichedDiagramJointComparison → IC.F1.Diagrams.RelativeSectionJointComparison |
| R64 | IC.F1.KanModels.KanEnrichedDiagramOppositeComparison |  禁止依存 744 本；IC.F1.KanModels.KanEnrichedDiagramOppositeComparison → IC.F1.Categories.KanDiagramNaturalTransformation |
| R64 | IC.F1.KanModels.KanEnrichedEdgewiseComparison |  禁止依存 730 本；IC.F1.KanModels.KanEnrichedEdgewiseComparison → IC.F1.KanModels.KanEnrichedDiagramComparison |
| R64 | IC.F1.KanModels.KanEnrichedHomInterval |  禁止依存 763 本；IC.F1.KanModels.KanEnrichedHomInterval → IC.F1.Categories.KanDiagramUniversalEnriched |
| R64 | IC.F1.KanModels.KanEnrichedHomIntervalNaturality |  禁止依存 777 本；IC.F1.KanModels.KanEnrichedHomIntervalNaturality → IC.F1.Coherent.HomEnrichedNaturality |
| R64 | IC.F1.KanModels.KanEnrichedHomIntervalPrecomposition |  禁止依存 778 本；IC.F1.KanModels.KanEnrichedHomIntervalPrecomposition → IC.F1.KanModels.KanEnrichedHomIntervalNaturality |
| R64 | IC.F1.KanModels.KanEnrichedLeftHomIntervalEvaluation |  禁止依存 805 本；IC.F1.KanModels.KanEnrichedLeftHomIntervalEvaluation → IC.F1.Coherent.LeftIntervalNaturality |
| R64 | IC.F1.KanModels.KanEnrichedTwoSidedHomInterval |  禁止依存 796 本；IC.F1.KanModels.KanEnrichedTwoSidedHomInterval → IC.F1.Coherent.TwoSidedHomLeftEndpoint |
| R64 | IC.F1.KanModels.KanEquivalenceLiftingFibration |  禁止依存 34 本；IC.F1.KanModels.KanEquivalenceLiftingFibration → IC.F2.CatInfinity.CoreIsofibration |
| R64 | IC.F1.KanModels.KanFibrationEquivalenceLifting |  禁止依存 344 本；IC.F1.KanModels.KanFibrationEquivalenceLifting → HA.Simplicial.UniverseLiftLifting |
| R64 | IC.F1.KanModels.KanOppositeCoefficients |  禁止依存 557 本；IC.F1.KanModels.KanOppositeCoefficients → IC.F1.KanModels.KanPointHomNaturality |
| R64 | IC.F1.KanModels.KanPointHomActionIso |  禁止依存 680 本；IC.F1.KanModels.KanPointHomActionIso → IC.F1.KanModels.KanPointHomEnriched |
| R64 | IC.F1.KanModels.KanPointHomEnriched |  禁止依存 679 本；IC.F1.KanModels.KanPointHomEnriched → IC.F1.KanModels.KanEnrichedComparisonIso |
| R64 | IC.F1.KanModels.KanPointHomNaturality |  禁止依存 124 本；IC.F1.KanModels.KanPointHomNaturality → IC.F1.StraighteningLeft.PointedSpaceMappingSpaces |
| R64 | IC.F1.KanModels.KanSpanPullbackComparison |  禁止依存 758 本；IC.F1.KanModels.KanSpanPullbackComparison → IC.F1.KanModels.KanFibrationEquivalenceLifting |
| R64 | IC.F1.KanModels.KanSquarePullbackEquivalence |  禁止依存 346 本；IC.F1.KanModels.KanSquarePullbackEquivalence → IC.F1.Equivalences.EquivalenceLiftingPullback |
| R64 | IC.F1.Simplicial.BoundaryRepresentationTransformationIso |  禁止依存 987 本；IC.F1.Simplicial.BoundaryRepresentationTransformationIso → IC.F1.FunctorCategories.EndpointPairTransformationVertices |
| R64 | IC.F1.Simplicial.FiniteCospanNerveEdges |  禁止依存 5 本；IC.F1.Simplicial.FiniteCospanNerveEdges → IC.F1.Simplicial.FiniteCospanNerveIso |
| R64 | IC.F1.Simplicial.FiniteCospanNerveIso |  禁止依存 4 本；IC.F1.Simplicial.FiniteCospanNerveIso → IC.F1B.NerveComparison.OppositeIso |
| R64 | IC.F1.Simplicial.FiniteHornUniverseIso |  禁止依存 6 本；IC.F1.Simplicial.FiniteHornUniverseIso → IC.F1.Simplicial.FiniteCospanNerveIso |
| R64 | IC.F1.Simplicial.FullPosetSubsetNerveIso |  禁止依存 1 本；IC.F1.Simplicial.FullPosetSubsetNerveIso → IC.F1B.NerveComparison.PosetLowerTerminalFunctor |
| R64 | IC.F1.Simplicial.InitialHornJoin |  禁止依存 1 本；IC.F1.Simplicial.InitialHornJoin → IC.F1.Fibrations.CartesianEdge |
| R64 | IC.F1.Simplicial.InnerAnodynePrismExtension |  禁止依存 3 本；IC.F1.Simplicial.InnerAnodynePrismExtension → IC.F1.Fibrations.CartesianEdge |
| R64 | IC.F1.Simplicial.InnerAnodyneVertices |  禁止依存 1 本；IC.F1.Simplicial.InnerAnodyneVertices → IC.F1.Fibrations.ThinNerveInnerFibration |
| R64 | IC.F1.Simplicial.InnerPrismBoundaryExtension |  禁止依存 732 本；IC.F1.Simplicial.InnerPrismBoundaryExtension → IC.F1.Simplicial.InnerAnodyneVertices |
| R64 | IC.F1.Simplicial.InnerTwoHornHomPullbacks |  禁止依存 924 本；IC.F1.Simplicial.InnerTwoHornHomPullbacks → IC.F1.Cocartesian.PullbackNativeCorePushout |
| R64 | IC.F1.Simplicial.PosetSubsetPointRemoval |  禁止依存 2 本；IC.F1.Simplicial.PosetSubsetPointRemoval → IC.F1.Simplicial.FullPosetSubsetNerveIso |
| R64 | IC.F1.Simplicial.PositivePathShiftIso |  禁止依存 377 本；IC.F1.Simplicial.PositivePathShiftIso → IC.F1.Fibrations.LeftPrismCutMinimumMaps |
| R64 | IC.F1.Simplicial.PreorderNerveHornExtension |  禁止依存 1 本；IC.F1.Simplicial.PreorderNerveHornExtension → IC.F1.Fibrations.ThinNerveInnerFibration |
| R64 | IC.F1.Simplicial.PrismBoundaryData |  禁止依存 65 本；IC.F1.Simplicial.PrismBoundaryData → IC.F1.Transport.VariableSourcePrismUniversal |
| R64 | IC.F1.Simplicial.PrismBoundaryLifting |  禁止依存 67 本；IC.F1.Simplicial.PrismBoundaryLifting → IC.F1.Simplicial.PrismBoundaryRecovery |
| R64 | IC.F1.Simplicial.PrismBoundaryRecovery |  禁止依存 66 本；IC.F1.Simplicial.PrismBoundaryRecovery → IC.F1.Simplicial.PrismBoundaryData |
| R64 | IC.F1.Simplicial.PrismCellPushout |  禁止依存 14 本；IC.F1.Simplicial.PrismCellPushout → IC.F1.Joins.RelativeJoinPrismHornEquality |
| R64 | IC.F1.Simplicial.PrismEndpointFiberIso |  禁止依存 811 本；IC.F1.Simplicial.PrismEndpointFiberIso → IC.F1.StraighteningLeft.PointedPrismSourceFiberTrivial |
| R64 | IC.F1.Simplicial.PrismEndpointPairPullback |  禁止依存 13 本；IC.F1.Simplicial.PrismEndpointPairPullback → IC.F1.Joins.JoinEndpointMaps |
| R64 | IC.F1.Simplicial.PrismRightConeBoundary |  禁止依存 12 本；IC.F1.Simplicial.PrismRightConeBoundary → IC.F1.Joins.RightConeJoin |
| R64 | IC.F1.Simplicial.PrismRightConeMap |  禁止依存 10 本；IC.F1.Simplicial.PrismRightConeMap → IC.F1.Joins.RelativeJoinConeMap |
| R64 | IC.F1.Simplicial.PrismRightConePullback |  禁止依存 32 本；IC.F1.Simplicial.PrismRightConePullback → IC.F1.Simplicial.PrismRightConeBoundary |
| R64 | IC.F1.Simplicial.PrismRightConeRange |  禁止依存 29 本；IC.F1.Simplicial.PrismRightConeRange → IC.F1.Joins.RelativeJoinStdSimplexVertices |
| R64 | IC.F1.Simplicial.PrismSourceFiberFibration |  禁止依存 809 本；IC.F1.Simplicial.PrismSourceFiberFibration → IC.F1.StraighteningLeft.PointedPrismEndpointFibration |
| R64 | IC.F1.Simplicial.PrismSourceVertexFiber |  禁止依存 800 本；IC.F1.Simplicial.PrismSourceVertexFiber → IC.F1.StraighteningLeft.PointedPrismFixedSourceEndpoint |
| R64 | IC.F1.Simplicial.ReplacementEndCornerInner |  禁止依存 751 本；IC.F1.Simplicial.ReplacementEndCornerInner → IC.F1.FunctorCategories.FullSubcomplexEquivalenceLifting |
| R64 | IC.F1.Simplicial.ReplacementInitialSubcomplex |  禁止依存 12 本；IC.F1.Simplicial.ReplacementInitialSubcomplex → IC.F1.Diagrams.SimplicialReplacementAssembly |
| R64 | IC.F1.Simplicial.ReplacementInnerHorn |  禁止依存 14 本；IC.F1.Simplicial.ReplacementInnerHorn → IC.F1.Scaffold.ScaffoldFiniteTail |
| R64 | IC.F1.Simplicial.ReplacementInnerHornPullback |  禁止依存 327 本；IC.F1.Simplicial.ReplacementInnerHornPullback → IC.F1.Scaffold.LeftScaffoldArbitraryBaseChange |
| R64 | IC.F1.Simplicial.ReplacementSpanComparison |  禁止依存 754 本；IC.F1.Simplicial.ReplacementSpanComparison → IC.F1.Joins.SpanPullbackLifting |
| R64 | IC.F1.Simplicial.ReplacementSquareResolution |  禁止依存 729 本；IC.F1.Simplicial.ReplacementSquareResolution → IC.F1.MappingSpaces.RelativePathEquivalenceFibration |
| R64 | IC.F1.Simplicial.ReplacementSquareStartCorner |  禁止依存 731 本；IC.F1.Simplicial.ReplacementSquareStartCorner → IC.F1.MappingSpaces.RelativePathEndpointCorner |
| R64 | IC.F1.Simplicial.SSetProductEvaluation |  禁止依存 82 本；IC.F1.Simplicial.SSetProductEvaluation → IC.F1.Yoneda.PresheafInfinity |
| R64 | IC.F1.Simplicial.SSetPullbackColimit |  禁止依存 2 本；IC.F1.Simplicial.SSetPullbackColimit → IC.F1.Limits.TypesPullbackColimit |
| R64 | IC.F1.Simplicial.SSetPullbackColimitDescent |  禁止依存 3 本；IC.F1.Simplicial.SSetPullbackColimitDescent → IC.F1.Simplicial.SSetPullbackColimit |
| R64 | IC.F1.Simplicial.SimplexAttachmentOver |  禁止依存 949 本；IC.F1.Simplicial.SimplexAttachmentOver → IC.F1.Cocartesian.CellAttachmentFibrations |
| R64 | IC.F1.Simplicial.SimplexNerveNaturality |  禁止依存 396 本；IC.F1.Simplicial.SimplexNerveNaturality → IC.F1.Simplicial.SimplexNerveOver |
| R64 | IC.F1.Simplicial.SimplexNerveOver |  禁止依存 395 本；IC.F1.Simplicial.SimplexNerveOver → IC.F1.Scaffold.ScaffoldFiniteNerveUniverse |
| R64 | IC.F1.Simplicial.SimplexNerveRestrictionOver |  禁止依存 641 本；IC.F1.Simplicial.SimplexNerveRestrictionOver → IC.F1.Cocartesian.BaseChangeNativeProjection |
| R64 | IC.F1.Simplicial.SimplexPrismFirstVertex |  禁止依存 20 本；IC.F1.Simplicial.SimplexPrismFirstVertex → IC.F1.Fibrations.LeftAnodynePushoutProduct |
| R64 | IC.F1.Simplicial.SimplexPrismParameterStart |  禁止依存 21 本；IC.F1.Simplicial.SimplexPrismParameterStart → IC.F1.Simplicial.SimplexPrismFirstVertex |
| R64 | IC.F1.Simplicial.SimplexShapeFamilyColimit |  禁止依存 722 本；IC.F1.Simplicial.SimplexShapeFamilyColimit → IC.F1.Simplicial.SimplexShapeFamilyPushout |
| R64 | IC.F1.Simplicial.SimplexShapeFamilyPushout |  禁止依存 721 本；IC.F1.Simplicial.SimplexShapeFamilyPushout → IC.F1.Transport.SimplexChainShape |
| R64 | IC.F1.Simplicial.SimplicialEnrichedOpposite |  禁止依存 66 本；IC.F1.Simplicial.SimplicialEnrichedOpposite → IC.F1.Coherent.NervePostcomposition |
| R64 | IC.F1.Simplicial.SimplicialHomConstantIdentity |  禁止依存 66 本；IC.F1.Simplicial.SimplicialHomConstantIdentity → IC.F1.Coherent.OrderDiagrams |
| R64 | IC.F1.Simplicial.SimplicialOverCategory |  禁止依存 300 本；IC.F1.Simplicial.SimplicialOverCategory → IC.F1.Fibrations.LeftFibrationInfinity |
| R64 | IC.F1.Simplicial.SimplicialOverJointOppositeTransport |  禁止依存 860 本；IC.F1.Simplicial.SimplicialOverJointOppositeTransport → IC.F1.Simplicial.SimplicialOverTestComparison |
| R64 | IC.F1.Simplicial.SimplicialOverTestBifunctor |  禁止依存 514 本；IC.F1.Simplicial.SimplicialOverTestBifunctor → IC.F1.FunctorCategories.RelativeFunctorActionEvaluation |
| R64 | IC.F1.Simplicial.SimplicialOverTestComparison |  禁止依存 688 本；IC.F1.Simplicial.SimplicialOverTestComparison → IC.F1.Fibrations.LeftFibrationCoherentEvaluation |
| R64 | IC.F1.Simplicial.SimplicialOverTestFamily |  禁止依存 1001 本；IC.F1.Simplicial.SimplicialOverTestFamily → IC.F1.Coherent.UniversalCoherentReconstructionComponents |
| R64 | IC.F1.Simplicial.SimplicialPairCategory |  禁止依存 419 本；IC.F1.Simplicial.SimplicialPairCategory → IC.F1.KanModels.KanEnrichedComparison |
| R64 | IC.F1.Simplicial.SimplicialPairLeftInclusion |  禁止依存 421 本；IC.F1.Simplicial.SimplicialPairLeftInclusion → IC.F1.Simplicial.SimplicialPairNerve |
| R64 | IC.F1.Simplicial.SimplicialPairNerve |  禁止依存 420 本；IC.F1.Simplicial.SimplicialPairNerve → IC.F1.Coherent.NervePostcomposition |
| R64 | IC.F1.Simplicial.StandardSimplexInnerFaceIndex |  禁止依存 9 本；IC.F1.Simplicial.StandardSimplexInnerFaceIndex → IC.F1.TwistedArrow.EdgewiseOutsideSimplices |
| R64 | IC.F1.Simplicial.StandardSimplexSupports |  禁止依存 4 本；IC.F1.Simplicial.StandardSimplexSupports → IC.F1.TwistedArrow.EdgewiseExtensionDomain |
| R64 | IC.F1.Simplicial.StdSimplexFiberFullyFaithful |  禁止依存 63 本；IC.F1.Simplicial.StdSimplexFiberFullyFaithful → IC.F1.Fibrations.ThinNerveInnerFibration |
| R64 | IC.F1.Simplicial.StdSimplexLastFaceFactor |  禁止依存 22 本；IC.F1.Simplicial.StdSimplexLastFaceFactor → IC.F1.Joins.RelativeJoinStdSimplexVertices |
| R64 | IC.F1.Simplicial.SubcomplexRestriction |  禁止依存 101 本；IC.F1.Simplicial.SubcomplexRestriction → IC.F1.Coherent.ResolutionFaceProjection |
| R64 | IC.F1.Simplicial.TwoSimplexSegalRestrictions |  禁止依存 1690 本；IC.F1.Simplicial.TwoSimplexSegalRestrictions → IC.F1.Cocartesian.PullbackRestrictionNaturality |
| R64 | IC.F1.Simplicial.UnderNerveDiagram |  禁止依存 79 本；IC.F1.Simplicial.UnderNerveDiagram → IC.F1.Transport.LeftStrictTransport |
| R64 | IC.F1B.KanComplex.HomotopyClasses | 衝突：HA.Simplicial.HomotopyClasses, IC.F1B.KanComplex.HomotopyClasses |
| R64 | IC.F1B.KanComplex.HomotopyDetection |  禁止依存 2 本；IC.F1B.KanComplex.HomotopyDetection → IC.F1B.KanComplex.HomotopyClasses |
| R64 | IC.F1B.KanComplex.HomotopyEquivalencePath |  禁止依存 55 本；IC.F1B.KanComplex.HomotopyEquivalencePath → IC.F1B.Homotopy.HomotopyRepresentative |
| R64 | IC.F1B.KanComplex.HomotopyMaximum |  禁止依存 40 本；IC.F1B.KanComplex.HomotopyMaximum → IC.F1B.Diagrams.IntervalMaximum |
| R64 | IC.F1B.KanComplex.HomotopyOfEq |  禁止依存 39 本；IC.F1B.KanComplex.HomotopyOfEq → IC.F1B.Homotopy.HomotopyWhiskering |
| R64 | IC.F1B.KanComplex.HomotopyOppositeLaws |  禁止依存 41 本；IC.F1B.KanComplex.HomotopyOppositeLaws → IC.F1B.FunctorCategories.FunctorOpposite |
| R64 | IC.F1B.KanComplex.HomotopyRepresentativeLift |  禁止依存 40 本；IC.F1B.KanComplex.HomotopyRepresentativeLift → IC.F1B.Fibrations.EdgeRepresentativeLift |
| R64 | KST.Comparison.ComponentHomotopy |  禁止依存 3 本；KST.Comparison.ComponentHomotopy → KST.Comparison.ComponentPointedSimplex |
| R64 | KST.Comparison.ComponentPointedSimplex |  禁止依存 2 本；KST.Comparison.ComponentPointedSimplex → KST.Comparison.ComponentKan |
| R64 | KST.Comparison.DiagramExInfinity |  禁止依存 184 本；KST.Comparison.DiagramExInfinity → KST.Comparison.ExInfinityHomotopyPullback |
| R64 | KST.Comparison.DoubleMappingCylinderCollapse |  禁止依存 60 本；KST.Comparison.DoubleMappingCylinderCollapse → KST.Comparison.LocalizedPushoutCube |
| R64 | KST.Comparison.DoubleMappingCylinderEquivalence |  禁止依存 61 本；KST.Comparison.DoubleMappingCylinderEquivalence → HA.Simplicial.AnodyneLocalizedTensor |
| R64 | KST.Comparison.ExInfinity |  禁止依存 2 本；KST.Comparison.ExInfinity → KST.Comparison.ExUnit |
| R64 | KST.Comparison.ExInfinityAnodyne |  禁止依存 36 本；KST.Comparison.ExInfinityAnodyne → KST.Comparison.ExInfinity |
| R64 | KST.Comparison.ExInfinityBar |  禁止依存 371 本；KST.Comparison.ExInfinityBar → KST.Comparison.BarLocalizedEquivalence |
| R64 | KST.Comparison.ExInfinityFibrations |  禁止依存 78 本；KST.Comparison.ExInfinityFibrations → HA.Diagram.ColimitWeakEquivalence |
| R64 | KST.Comparison.ExInfinityGrouplike |  禁止依存 225 本；KST.Comparison.ExInfinityGrouplike → KST.Comparison.ExInfinitySimplicialMonoid |
| R64 | KST.Comparison.ExInfinityHomotopyPullback |  禁止依存 163 本；KST.Comparison.ExInfinityHomotopyPullback → KST.Comparison.HomotopyPullbackThreeInputs |
| R64 | KST.Comparison.ExInfinityKan |  禁止依存 22 本；KST.Comparison.ExInfinityKan → KST.Comparison.ExDoubleHornFiller |
| R64 | KST.Comparison.ExInfinityLocalization |  禁止依存 75 本；KST.Comparison.ExInfinityLocalization → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | KST.Comparison.ExInfinityMonoidal |  禁止依存 76 本；KST.Comparison.ExInfinityMonoidal → KST.Comparison.ExInfinityLocalization |
| R64 | KST.Comparison.ExInfinitySimplicialMonoid |  禁止依存 211 本；KST.Comparison.ExInfinitySimplicialMonoid → KST.Comparison.ExInfinityMonoidal |
| R64 | KST.Comparison.ExInfinityStages |  禁止依存 3 本；KST.Comparison.ExInfinityStages → KST.Comparison.ExInfinity |
| R64 | KST.Comparison.ExUnitAnodyne |  禁止依存 34 本；KST.Comparison.ExUnitAnodyne → KST.Comparison.ExPairingRegular |
| R64 | KST.Comparison.FatBoundaryHomotopyPullback |  禁止依存 300 本；KST.Comparison.FatBoundaryHomotopyPullback → KST.Comparison.BoundaryFaceRepresentation |
| R64 | KST.Comparison.FatRealizationHomotopyPullback |  禁止依存 349 本；KST.Comparison.FatRealizationHomotopyPullback → KST.Comparison.ActualSequentialComparison |
| R64 | KST.Comparison.FatSkeletonHomotopyPullback |  禁止依存 334 本；KST.Comparison.FatSkeletonHomotopyPullback → KST.Comparison.FatSkeletonSuccessor |
| R64 | KST.Comparison.FiberwiseAnodyne |  禁止依存 18 本；KST.Comparison.FiberwiseAnodyne → HA.Simplicial.AnodyneIntervalEndpoints |
| R64 | KST.Comparison.FunctorHomotopyPullbacks |  禁止依存 25 本；KST.Comparison.FunctorHomotopyPullbacks → KST.Comparison.AlternativePullback |
| R64 | KST.Comparison.GroupCompletionHomotopy |  禁止依存 686 本；KST.Comparison.GroupCompletionHomotopy → KST.Comparison.GroupCompletionBasepoint |
| R64 | KST.Comparison.HatGLCoefficientHomotopy |  禁止依存 140 本；KST.Comparison.HatGLCoefficientHomotopy → KST.Comparison.HatGLPositiveHomotopy |
| R64 | KST.Comparison.HatGLPositiveHomotopy |  禁止依存 136 本；KST.Comparison.HatGLPositiveHomotopy → KST.Comparison.ComponentHomotopy |
| R64 | KST.Comparison.HomologyAnodyne |  禁止依存 37 本；KST.Comparison.HomologyAnodyne → KST.Comparison.HomologyHorn |
| R64 | KST.Comparison.HomologyHomotopy |  禁止依存 1 本；KST.Comparison.HomologyHomotopy → KST.Comparison.Homology |
| R64 | KST.Comparison.HomotopyPullback |  禁止依存 19 本；KST.Comparison.HomotopyPullback → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | KST.Comparison.HomotopyPullbackGeneralPasting |  禁止依存 169 本；KST.Comparison.HomotopyPullbackGeneralPasting → KST.Comparison.KanSquareReplacement |
| R64 | KST.Comparison.HomotopyPullbackInvariance |  禁止依存 160 本；KST.Comparison.HomotopyPullbackInvariance → KST.Comparison.FibrantPullbackMap |
| R64 | KST.Comparison.HomotopyPullbackPasting |  禁止依存 167 本；KST.Comparison.HomotopyPullbackPasting → KST.Comparison.FibrantSquareCriterion |
| R64 | KST.Comparison.HomotopyPullbackSymmetry |  禁止依存 165 本；KST.Comparison.HomotopyPullbackSymmetry → KST.Comparison.AlternativePullback |
| R64 | KST.Comparison.HomotopyPullbackThreeInputs |  禁止依存 162 本；KST.Comparison.HomotopyPullbackThreeInputs → KST.Comparison.FibrantCospanInvariance |
| R64 | KST.Comparison.HornFaceInclusionAnodyne |  禁止依存 32 本；KST.Comparison.HornFaceInclusionAnodyne → KST.Comparison.FiniteChainUnion |
| R64 | KST.Comparison.HornSimplexFaceFactorization |  禁止依存 17 本；KST.Comparison.HornSimplexFaceFactorization → KST.Comparison.HornSubdivisionSurjective |
| R64 | KST.Comparison.KanAnodyneBaseChange |  禁止依存 51 本；KST.Comparison.KanAnodyneBaseChange → HA.Simplicial.KanTestLiftingClass |
| R64 | KST.Comparison.LocalCoefficientAnodyne |  禁止依存 58 本；KST.Comparison.LocalCoefficientAnodyne → KST.Comparison.LocalCoefficientHorn |
| R64 | KST.Comparison.LocalizedHomotopyComparison |  禁止依存 103 本；KST.Comparison.LocalizedHomotopyComparison → HA.Simplicial.KanFibrationLocalizedLifting |
| R64 | KST.Comparison.MappingCylinder |  禁止依存 18 本；KST.Comparison.MappingCylinder → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | KST.Comparison.MappingCylinderDouble |  禁止依存 19 本；KST.Comparison.MappingCylinderDouble → KST.Comparison.MappingCylinder |
| R64 | KST.Comparison.MatrixHomotopyProduct |  禁止依存 131 本；KST.Comparison.MatrixHomotopyProduct → KST.Comparison.MatrixPointedSimplex |
| R64 | KST.Comparison.MatrixPointedSimplex |  禁止依存 130 本；KST.Comparison.MatrixPointedSimplex → KST.Comparison.MatrixSpace |
| R64 | KST.Comparison.PairContractionAnodyne |  禁止依存 22 本；KST.Comparison.PairContractionAnodyne → KST.Comparison.PairHomotopyLifting |
| R64 | KST.Comparison.PairHomotopyLifting |  禁止依存 19 本；KST.Comparison.PairHomotopyLifting → KST.Comparison.FiberwiseAnodyne |
| R64 | KST.Comparison.ProductHomotopyPullback |  禁止依存 25 本；KST.Comparison.ProductHomotopyPullback → KST.Comparison.AlternativePullback |
| R64 | KST.Comparison.RegularBarHomotopyFiber |  禁止依存 579 本；KST.Comparison.RegularBarHomotopyFiber → KST.Comparison.BarZeroEvaluation |
| R64 | KST.Comparison.SequenceHomotopyPullbacks |  禁止依存 188 本；KST.Comparison.SequenceHomotopyPullbacks → KST.Comparison.HomotopyPullbackPasting |
| R64 | KST.Comparison.SequentialHomotopyPullback |  禁止依存 187 本；KST.Comparison.SequentialHomotopyPullback → HA.Simplicial.KanSequentialColimitComparison |
| R64 | KST.Comparison.SimplexFaceRetraction |  禁止依存 2 本；KST.Comparison.SimplexFaceRetraction → KST.Comparison.SubdivisionNerveChains |
| R64 | KST.Comparison.SimplicialMonoidInternal |  禁止依存 133 本；KST.Comparison.SimplicialMonoidInternal → KST.Comparison.MonoidComponents |
| R64 | KST.Comparison.SimplicialRingKan |  禁止依存 5 本；KST.Comparison.SimplicialRingKan → KST.Comparison.RingHornUpper |
| R64 | KST.Comparison.SimplicialSumEquivalences |  禁止依存 45 本；KST.Comparison.SimplicialSumEquivalences → HA.Simplicial.KanLocalizedCoproducts |
| R64 | KST.Comparison.SimplicialSumFibrations |  禁止依存 1 本；KST.Comparison.SimplicialSumFibrations → KST.Comparison.FibrationLocality |
| R64 | KST.Comparison.SimplicialSumHomotopyPullbacks |  禁止依存 171 本；KST.Comparison.SimplicialSumHomotopyPullbacks → KST.Comparison.FibrantSquareCriterion |
| R64 | KST.Comparison.StableHatGLHomotopyColimit |  禁止依存 715 本；KST.Comparison.StableHatGLHomotopyColimit → KST.Comparison.StableHatGLKan |
| R64 | KST.Comparison.StableHatGLHomotopyGroupColimit |  禁止依存 718 本；KST.Comparison.StableHatGLHomotopyGroupColimit → KST.Comparison.CoefficientMatrixStabilization |
| R64 | KST.Comparison.StrictCylinderHomotopyPullbacks |  禁止依存 175 本；KST.Comparison.StrictCylinderHomotopyPullbacks → KST.Comparison.FibrantPullbackComparison |
| R64 | KST.Comparison.SubdivisionAdjunctionSimplex |  禁止依存 4 本；KST.Comparison.SubdivisionAdjunctionSimplex → KST.Comparison.SubdivisionLastVertexSimplex |
| R64 | KST.Comparison.SubdivisionAnodyne |  禁止依存 49 本；KST.Comparison.SubdivisionAnodyne → KST.Comparison.HornFaceInclusionAnodyne |
| R64 | KST.Comparison.SubdivisionLastVertexSimplex |  禁止依存 3 本；KST.Comparison.SubdivisionLastVertexSimplex → KST.Comparison.SubdivisionLastVertexMap |
| R64 | KST.Comparison.TensorHomotopyPullbacks |  禁止依存 31 本；KST.Comparison.TensorHomotopyPullbacks → HA.Simplicial.AnodyneLocalizedTensor |
| R56a | KST.LocalizingInvariants.CoreAnodyneLifting |  禁止依存 3 本；KST.LocalizingInvariants.CoreAnodyneLifting → IC.F2.CatInfinity.CoreIsofibration |
| R56a | KST.LocalizingInvariants.GeneralLocalization |  禁止依存 23 本；KST.LocalizingInvariants.GeneralLocalization → KST.LocalizingInvariants.LocalizationResolution |
| R56a | KST.LocalizingInvariants.InverseAttachment |  禁止依存 18 本；KST.LocalizingInvariants.InverseAttachment → KST.LocalizingInvariants.WalkingEquivalenceUniversal |
| R56a | KST.LocalizingInvariants.InverseAttachmentLifting |  禁止依存 20 本；KST.LocalizingInvariants.InverseAttachmentLifting → KST.LocalizingInvariants.InverseAttachmentRestriction |
| R56a | KST.LocalizingInvariants.InverseAttachmentRestriction |  禁止依存 19 本；KST.LocalizingInvariants.InverseAttachmentRestriction → KST.LocalizingInvariants.InverseAttachment |
| R56a | KST.LocalizingInvariants.InverseAttachmentUniversal |  禁止依存 21 本；KST.LocalizingInvariants.InverseAttachmentUniversal → KST.LocalizingInvariants.InverseAttachmentLifting |
| R56a | KST.LocalizingInvariants.LocalizationFactorization |  禁止依存 24 本；KST.LocalizingInvariants.LocalizationFactorization → KST.LocalizingInvariants.GeneralLocalization |
| R56a | KST.LocalizingInvariants.LocalizationResolution |  禁止依存 22 本；KST.LocalizingInvariants.LocalizationResolution → KST.LocalizingInvariants.InverseAttachmentUniversal |
| R56a | KST.LocalizingInvariants.LocalizationUniqueness |  禁止依存 25 本；KST.LocalizingInvariants.LocalizationUniqueness → KST.LocalizingInvariants.LocalizationFactorization |
| R56a | KST.LocalizingInvariants.WalkingEquivalence |  禁止依存 15 本；KST.LocalizingInvariants.WalkingEquivalence → KST.LocalizingInvariants.CoreAnodyneLifting |
| R56a | KST.LocalizingInvariants.WalkingEquivalenceRestriction |  禁止依存 16 本；KST.LocalizingInvariants.WalkingEquivalenceRestriction → KST.LocalizingInvariants.WalkingEquivalence |
| R56a | KST.LocalizingInvariants.WalkingEquivalenceUniversal |  禁止依存 17 本；KST.LocalizingInvariants.WalkingEquivalenceUniversal → KST.LocalizingInvariants.WalkingEquivalenceRestriction |
| R64 | KST.SConstruction.CoherentArrowNativeFamilies |  禁止依存 714 本；KST.SConstruction.CoherentArrowNativeFamilies → IC.F1B.Homotopy.HomotopyWhiskering |
| R64 | KST.SConstruction.CoherentArrowStringInitial |  禁止依存 693 本；KST.SConstruction.CoherentArrowStringInitial → IC.F1.FunctorCategories.OrdinaryComparisonPrism |
| R64 | KST.SConstruction.CoherentPathActionConstancy |  禁止依存 71 本；KST.SConstruction.CoherentPathActionConstancy → KST.SConstruction.CoherentStrictPathEvaluation |
| R64 | KST.SConstruction.CoherentPathInsertion |  禁止依存 695 本；KST.SConstruction.CoherentPathInsertion → IC.Coherent.CompositionFace |
| R64 | KST.SConstruction.CoherentPathInsertionDiamond |  禁止依存 696 本；KST.SConstruction.CoherentPathInsertionDiamond → KST.SConstruction.CoherentPathInsertion |
| R64 | KST.SConstruction.CoherentPathMappingHomotopy |  禁止依存 710 本；KST.SConstruction.CoherentPathMappingHomotopy → IC.F1B.Homotopy.HomotopyWhiskering |
| R64 | KST.SConstruction.CoherentStringDiagramCells |  禁止依存 67 本；KST.SConstruction.CoherentStringDiagramCells → IC.Coherent.FunctorReindex |
| R64 | KST.SConstruction.CoherentStringFullPaths |  禁止依存 695 本；KST.SConstruction.CoherentStringFullPaths → KST.SConstruction.CoherentArrowStringInitial |
| R64 | KST.SConstruction.CoherentStringNativeMaps |  禁止依存 80 本；KST.SConstruction.CoherentStringNativeMaps → IC.F1.Coherent.HomMono |
| R64 | KST.SConstruction.CompositionTripleHorns |  禁止依存 83 本；KST.SConstruction.CompositionTripleHorns → KST.SConstruction.HornHomExt |
| R64 | KST.SConstruction.CompositionTripleInputTransport |  禁止依存 85 本；KST.SConstruction.CompositionTripleInputTransport → KST.SConstruction.CompositionTripleTetrahedronLifting |
| R64 | KST.SConstruction.CompositionTripleTetrahedronLifting |  禁止依存 84 本；KST.SConstruction.CompositionTripleTetrahedronLifting → KST.SConstruction.CompositionTripleHorns |
| R64 | KST.SConstruction.ConcreteCubeDimensionIso |  禁止依存 159 本；KST.SConstruction.ConcreteCubeDimensionIso → KST.SConstruction.ConcreteCubeTensor |
| R64 | KST.SConstruction.ConcreteCubeFaceConjugation |  禁止依存 162 本；KST.SConstruction.ConcreteCubeFaceConjugation → KST.SConstruction.ConcreteCubeFaceCriterion |
| R64 | KST.SConstruction.ConcreteCubeFaceCriterion |  禁止依存 161 本；KST.SConstruction.ConcreteCubeFaceCriterion → KST.SConstruction.ConcreteCubeZeroFaceCriterion |
| R64 | KST.SConstruction.ConcreteCubeMonoidal |  禁止依存 162 本；KST.SConstruction.ConcreteCubeMonoidal → KST.SConstruction.ConcreteCubeTensorCoherence |
| R64 | KST.SConstruction.ConcreteCubeRightBlockHom |  禁止依存 160 本；KST.SConstruction.ConcreteCubeRightBlockHom → KST.SConstruction.ConcreteCubeRightBlockMaps |
| R64 | KST.SConstruction.ConcreteCubeRightBlockMaps |  禁止依存 159 本；KST.SConstruction.ConcreteCubeRightBlockMaps → KST.SConstruction.ConcreteCubeTensor |
| R64 | KST.SConstruction.ConcreteCubeTensor |  禁止依存 157 本；KST.SConstruction.ConcreteCubeTensor → KST.SConstruction.CubeThreeNormalTensor |
| R64 | KST.SConstruction.ConcreteCubeTensorCoherence |  禁止依存 161 本；KST.SConstruction.ConcreteCubeTensorCoherence → KST.SConstruction.ConcreteCubeTensorNaturality |
| R64 | KST.SConstruction.ConcreteCubeTensorNaturality |  禁止依存 160 本；KST.SConstruction.ConcreteCubeTensorNaturality → KST.SConstruction.ConcreteCubeDimensionIso |
| R64 | KST.SConstruction.ConcreteCubeTensorWhisker |  禁止依存 158 本；KST.SConstruction.ConcreteCubeTensorWhisker → KST.SConstruction.ConcreteCubeTensor |
| R64 | KST.SConstruction.ConcreteCubeZeroFaceCriterion |  禁止依存 160 本；KST.SConstruction.ConcreteCubeZeroFaceCriterion → KST.SConstruction.ConcreteCubeDimensionIso |
| R64 | KST.SConstruction.CubeConnectionDeletionExpression |  禁止依存 126 本；KST.SConstruction.CubeConnectionDeletionExpression → KST.SConstruction.CubeDeletionConnectionUpdates |
| R64 | KST.SConstruction.CubeConnectionDeletionPathNormalization |  禁止依存 127 本；KST.SConstruction.CubeConnectionDeletionPathNormalization → KST.SConstruction.CubeConnectionDeletionExpression |
| R64 | KST.SConstruction.CubeConnectionExpression |  禁止依存 103 本；KST.SConstruction.CubeConnectionExpression → KST.SConstruction.SerreCubeConnectionNormal |
| R64 | KST.SConstruction.CubeConnectionNormal |  禁止依存 91 本；KST.SConstruction.CubeConnectionNormal → KST.SConstruction.CubeFacePathIndependence |
| R64 | KST.SConstruction.CubeConnectionNormalDeletion |  禁止依存 116 本；KST.SConstruction.CubeConnectionNormalDeletion → KST.SConstruction.CubeDeletionConnectionNormal |
| R64 | KST.SConstruction.CubeConnectionNormalDetection |  禁止依存 92 本；KST.SConstruction.CubeConnectionNormalDetection → KST.SConstruction.CubeConnectionNormal |
| R64 | KST.SConstruction.CubeConnectionPathEvaluation |  禁止依存 104 本；KST.SConstruction.CubeConnectionPathEvaluation → KST.SConstruction.CubeConnectionExpression |
| R64 | KST.SConstruction.CubeConnectionPathIndependence |  禁止依存 105 本；KST.SConstruction.CubeConnectionPathIndependence → KST.SConstruction.CubeConnectionPathEvaluation |
| R64 | KST.SConstruction.CubeConnectionVertexRecursion |  禁止依存 114 本；KST.SConstruction.CubeConnectionVertexRecursion → KST.SConstruction.CubeFaceDeletionPathNormalization |
| R64 | KST.SConstruction.CubeDeletionConnectionDetection |  禁止依存 140 本；KST.SConstruction.CubeDeletionConnectionDetection → KST.SConstruction.CubeDeletionNormalUsed |
| R64 | KST.SConstruction.CubeDeletionConnectionNormal |  禁止依存 115 本；KST.SConstruction.CubeDeletionConnectionNormal → KST.SConstruction.CubeConnectionVertexRecursion |
| R64 | KST.SConstruction.CubeDeletionConnectionUpdates |  禁止依存 125 本；KST.SConstruction.CubeDeletionConnectionUpdates → KST.SConstruction.CubeDeletionNormalComposition |
| R64 | KST.SConstruction.CubeDeletionExpression |  禁止依存 80 本；KST.SConstruction.CubeDeletionExpression → KST.SConstruction.SerreCubeDeletionNormal |
| R64 | KST.SConstruction.CubeDeletionFaceNormal |  禁止依存 110 本；KST.SConstruction.CubeDeletionFaceNormal → KST.SConstruction.SerreCubeFaceDeletionResult |
| R64 | KST.SConstruction.CubeDeletionNormalComposition |  禁止依存 80 本；KST.SConstruction.CubeDeletionNormalComposition → KST.SConstruction.SerreCubeDeletionNormal |
| R64 | KST.SConstruction.CubeDeletionNormalUsed |  禁止依存 139 本；KST.SConstruction.CubeDeletionNormalUsed → KST.SConstruction.CubeNormalEndpoints |
| R64 | KST.SConstruction.CubeDeletionPathEvaluation |  禁止依存 82 本；KST.SConstruction.CubeDeletionPathEvaluation → KST.SConstruction.CubeDeletionExpression |
| R64 | KST.SConstruction.CubeDeletionPathIndependence |  禁止依存 83 本；KST.SConstruction.CubeDeletionPathIndependence → KST.SConstruction.CubeDeletionPathEvaluation |
| R64 | KST.SConstruction.CubeFaceConnectionPathNormalization |  禁止依存 137 本；KST.SConstruction.CubeFaceConnectionPathNormalization → KST.SConstruction.CubeThreeNormal |
| R64 | KST.SConstruction.CubeFaceConnectionResult |  禁止依存 128 本；KST.SConstruction.CubeFaceConnectionResult → KST.SConstruction.CubeConnectionDeletionPathNormalization |
| R64 | KST.SConstruction.CubeFaceDeletionExpression |  禁止依存 112 本；KST.SConstruction.CubeFaceDeletionExpression → KST.SConstruction.SerreCubeDeletionFaceNormal |
| R64 | KST.SConstruction.CubeFaceDeletionPathNormalization |  禁止依存 113 本；KST.SConstruction.CubeFaceDeletionPathNormalization → KST.SConstruction.CubeFaceDeletionExpression |
| R64 | KST.SConstruction.CubeFaceDeletionResult |  禁止依存 106 本；KST.SConstruction.CubeFaceDeletionResult → KST.SConstruction.CubeConnectionPathIndependence |
| R64 | KST.SConstruction.CubeFaceExpression |  禁止依存 88 本；KST.SConstruction.CubeFaceExpression → KST.SConstruction.SerreCubeFaceNormal |
| R64 | KST.SConstruction.CubeFaceNormal |  禁止依存 84 本；KST.SConstruction.CubeFaceNormal → KST.SConstruction.CubeDeletionPathIndependence |
| R64 | KST.SConstruction.CubeFaceNormalConnection |  禁止依存 129 本；KST.SConstruction.CubeFaceNormalConnection → KST.SConstruction.CubeFaceConnectionResult |
| R64 | KST.SConstruction.CubeFaceNormalDeletion |  禁止依存 107 本；KST.SConstruction.CubeFaceNormalDeletion → KST.SConstruction.CubeFaceDeletionResult |
| R64 | KST.SConstruction.CubeFaceNormalDetection |  禁止依存 85 本；KST.SConstruction.CubeFaceNormalDetection → KST.SConstruction.CubeFaceNormal |
| R64 | KST.SConstruction.CubeFacePathEvaluation |  禁止依存 89 本；KST.SConstruction.CubeFacePathEvaluation → KST.SConstruction.CubeFaceExpression |
| R64 | KST.SConstruction.CubeFacePathIndependence |  禁止依存 90 本；KST.SConstruction.CubeFacePathIndependence → KST.SConstruction.CubeFacePathEvaluation |
| R64 | KST.SConstruction.CubeKeepInterchange |  禁止依存 152 本；KST.SConstruction.CubeKeepInterchange → KST.SConstruction.CubeLeftWhisker |
| R64 | KST.SConstruction.CubeLeftKeep |  禁止依存 149 本；KST.SConstruction.CubeLeftKeep → KST.SConstruction.CubeLeftKeepCoordinates |
| R64 | KST.SConstruction.CubeLeftKeepCoordinates |  禁止依存 148 本；KST.SConstruction.CubeLeftKeepCoordinates → KST.SConstruction.CubeRightKeep |
| R64 | KST.SConstruction.CubeLeftWhisker |  禁止依存 150 本；KST.SConstruction.CubeLeftWhisker → KST.SConstruction.CubeLeftKeep |
| R64 | KST.SConstruction.CubeMixedExpression |  禁止依存 139 本；KST.SConstruction.CubeMixedExpression → KST.SConstruction.CubeThreeNormalUpdates |
| R64 | KST.SConstruction.CubeMixedPathNormalization |  禁止依存 140 本；KST.SConstruction.CubeMixedPathNormalization → KST.SConstruction.CubeMixedExpression |
| R64 | KST.SConstruction.CubeNormalEndpoints |  禁止依存 138 本；KST.SConstruction.CubeNormalEndpoints → KST.SConstruction.CubeThreeNormalResults |
| R64 | KST.SConstruction.CubeNormalGenerated |  禁止依存 155 本；KST.SConstruction.CubeNormalGenerated → KST.SConstruction.CubeMixedPathNormalization |
| R64 | KST.SConstruction.CubeNormalTensor |  禁止依存 154 本；KST.SConstruction.CubeNormalTensor → KST.SConstruction.CubeVertexBlocks |
| R64 | KST.SConstruction.CubePathNaturality |  禁止依存 150 本；KST.SConstruction.CubePathNaturality → KST.SConstruction.CubeLeftKeep |
| R64 | KST.SConstruction.CubeRightKeep |  禁止依存 147 本；KST.SConstruction.CubeRightKeep → KST.SConstruction.SerreConcreteCubeFunctor |
| R64 | KST.SConstruction.CubeRightKeepHom |  禁止依存 148 本；KST.SConstruction.CubeRightKeepHom → KST.SConstruction.CubeRightKeep |
| R64 | KST.SConstruction.CubeRightWhisker |  禁止依存 150 本；KST.SConstruction.CubeRightWhisker → KST.SConstruction.CubeLeftKeep |
| R64 | KST.SConstruction.CubeThreeNormal |  禁止依存 136 本；KST.SConstruction.CubeThreeNormal → KST.SConstruction.SerreCubeFaceNormalConnection |
| R64 | KST.SConstruction.CubeThreeNormalDetection |  禁止依存 141 本；KST.SConstruction.CubeThreeNormalDetection → KST.SConstruction.CubeDeletionConnectionDetection |
| R64 | KST.SConstruction.CubeThreeNormalResults |  禁止依存 137 本；KST.SConstruction.CubeThreeNormalResults → KST.SConstruction.CubeThreeNormal |
| R64 | KST.SConstruction.CubeThreeNormalTensor |  禁止依存 156 本；KST.SConstruction.CubeThreeNormalTensor → KST.SConstruction.CubeNormalGenerated |
| R64 | KST.SConstruction.CubeThreeNormalUpdates |  禁止依存 138 本；KST.SConstruction.CubeThreeNormalUpdates → KST.SConstruction.CubeThreeNormalResults |
| R64 | KST.SConstruction.CubeVertexBlockCoordinates |  禁止依存 154 本；KST.SConstruction.CubeVertexBlockCoordinates → KST.SConstruction.CubeVertexBlocks |
| R64 | KST.SConstruction.CubeVertexBlocks |  禁止依存 153 本；KST.SConstruction.CubeVertexBlocks → KST.SConstruction.CubeKeepInterchange |
| R64 | KST.SConstruction.CubeVertexTransport |  禁止依存 154 本；KST.SConstruction.CubeVertexTransport → KST.SConstruction.CubeVertexBlocks |
| R64 | KST.SConstruction.CubeWordRightKeep |  禁止依存 151 本；KST.SConstruction.CubeWordRightKeep → KST.SConstruction.CubePathNaturality |
| R64 | KST.SConstruction.CubicalDayBicolimit |  禁止依存 172 本；KST.SConstruction.CubicalDayBicolimit → KST.SConstruction.CubicalDayColimits |
| R64 | KST.SConstruction.CubicalDayCells |  禁止依存 165 本；KST.SConstruction.CubicalDayCells → KST.SConstruction.CubicalDayTensor |
| R64 | KST.SConstruction.CubicalDayColimits |  禁止依存 171 本；KST.SConstruction.CubicalDayColimits → KST.SConstruction.CubicalDayKanComparison |
| R64 | KST.SConstruction.CubicalDayKanComparison |  禁止依存 167 本；KST.SConstruction.CubicalDayKanComparison → KST.SConstruction.CubicalDayTensorLaws |
| R64 | KST.SConstruction.CubicalDayRepresentable |  禁止依存 166 本；KST.SConstruction.CubicalDayRepresentable → KST.SConstruction.CubicalDayCells |
| R64 | KST.SConstruction.CubicalDayRepresentableNaturality |  禁止依存 168 本；KST.SConstruction.CubicalDayRepresentableNaturality → KST.SConstruction.CubicalDayRepresentable |
| R64 | KST.SConstruction.CubicalDayStructuralCells |  禁止依存 168 本；KST.SConstruction.CubicalDayStructuralCells → KST.SConstruction.CubicalDayTensorLaws |
| R64 | KST.SConstruction.CubicalDayTensor |  禁止依存 164 本；KST.SConstruction.CubicalDayTensor → KST.SConstruction.ConcreteCubeMonoidal |
| R64 | KST.SConstruction.CubicalDayTensorLaws |  禁止依存 166 本；KST.SConstruction.CubicalDayTensorLaws → KST.SConstruction.CubicalDayCells |
| R64 | KST.SConstruction.CubicalDayUnit |  禁止依存 165 本；KST.SConstruction.CubicalDayUnit → KST.SConstruction.CubicalDayTensor |
| R64 | KST.SConstruction.CubicalDayWrappedColimits |  禁止依存 172 本；KST.SConstruction.CubicalDayWrappedColimits → KST.SConstruction.CubicalDayColimits |
| R64 | KST.SConstruction.CubicalDayYonedaAssociativity |  禁止依存 172 本；KST.SConstruction.CubicalDayYonedaAssociativity → KST.SConstruction.CubicalDayStructuralCells |
| R64 | KST.SConstruction.CubicalDayYonedaData |  禁止依存 170 本；KST.SConstruction.CubicalDayYonedaData → KST.SConstruction.CubicalDayRepresentableNaturality |
| R64 | KST.SConstruction.CubicalDayYonedaMonoidal |  禁止依存 174 本；KST.SConstruction.CubicalDayYonedaMonoidal → KST.SConstruction.CubicalDayYonedaAssociativity |
| R64 | KST.SConstruction.CubicalDayYonedaRecovery |  禁止依存 175 本；KST.SConstruction.CubicalDayYonedaRecovery → KST.SConstruction.CubicalDayYonedaMonoidal |
| R64 | KST.SConstruction.CubicalDayYonedaUnitCoherence |  禁止依存 172 本；KST.SConstruction.CubicalDayYonedaUnitCoherence → KST.SConstruction.CubicalDayStructuralCells |
| R64 | KST.SConstruction.CubicalExternalColimits |  禁止依存 165 本；KST.SConstruction.CubicalExternalColimits → KST.SConstruction.CubicalDayTensor |
| R64 | KST.SConstruction.CubicalLambda |  禁止依存 255 本；KST.SConstruction.CubicalLambda → DifferentialGraded.Category.Basic |
| R64 | KST.SConstruction.CubicalLambdaComonoids |  禁止依存 267 本；KST.SConstruction.CubicalLambdaComonoids → KST.SConstruction.CubicalLambda |
| R64 | KST.SConstruction.CubicalLambdaCounit |  禁止依存 272 本；KST.SConstruction.CubicalLambdaCounit → DifferentialGraded.Category.Examples |
| R64 | KST.SConstruction.CubicalLambdaDiagonal |  禁止依存 271 本；KST.SConstruction.CubicalLambdaDiagonal → DifferentialGraded.Category.Tensor |
| R64 | KST.SConstruction.CubicalLambdaDiagonalCoherence |  禁止依存 274 本；KST.SConstruction.CubicalLambdaDiagonalCoherence → KST.SConstruction.CubicalLambdaDiagonal |
| R64 | KST.SConstruction.CubicalLambdaFunctorPair |  禁止依存 272 本；KST.SConstruction.CubicalLambdaFunctorPair → KST.SConstruction.CubicalLambdaDiagonal |
| R64 | KST.SConstruction.CubicalLambdaFunctorPairCoherence |  禁止依存 279 本；KST.SConstruction.CubicalLambdaFunctorPairCoherence → KST.SConstruction.ComonoidFunctorPairLaws |
| R64 | KST.SConstruction.CubicalLambdaHorizontalCoherence |  禁止依存 303 本；KST.SConstruction.CubicalLambdaHorizontalCoherence → KST.SConstruction.CubicalLambdaFunctorPairCoherence |
| R64 | KST.SConstruction.CubicalLambdaNativeCellComponent |  禁止依存 296 本；KST.SConstruction.CubicalLambdaNativeCellComponent → KST.SConstruction.CubicalLambdaNativeSimplexData |
| R64 | KST.SConstruction.CubicalLambdaNativeCollapsedHigher |  禁止依存 346 本；KST.SConstruction.CubicalLambdaNativeCollapsedHigher → KST.SConstruction.CubicalLambdaNativeNoninjectiveImage |
| R64 | KST.SConstruction.CubicalLambdaNativeCollapsedPair |  禁止依存 458 本；KST.SConstruction.CubicalLambdaNativeCollapsedPair → KST.SConstruction.CubicalLambdaNativeNormalizedComponent |
| R64 | KST.SConstruction.CubicalLambdaNativeCoordinateBoundary |  禁止依存 359 本；KST.SConstruction.CubicalLambdaNativeCoordinateBoundary → KST.SConstruction.CubicalLambdaNativeFaceTerm |
| R64 | KST.SConstruction.CubicalLambdaNativeDifferentialBoundary |  禁止依存 363 本；KST.SConstruction.CubicalLambdaNativeDifferentialBoundary → KST.SConstruction.SerreCubeTopCellImageDifferentialTransport |
| R64 | KST.SConstruction.CubicalLambdaNativeEdgeEquation |  禁止依存 296 本；KST.SConstruction.CubicalLambdaNativeEdgeEquation → KST.SConstruction.CubicalLambdaNativeSimplexData |
| R64 | KST.SConstruction.CubicalLambdaNativeFaceTerm |  禁止依存 356 本；KST.SConstruction.CubicalLambdaNativeFaceTerm → KST.SConstruction.SimplexSubsetMappedOneFaceTop |
| R64 | KST.SConstruction.CubicalLambdaNativeInjectiveComponent |  禁止依存 457 本；KST.SConstruction.CubicalLambdaNativeInjectiveComponent → KST.SConstruction.CubicalLambdaNativeNormalizedComponent |
| R64 | KST.SConstruction.CubicalLambdaNativeInjectiveNaturality |  禁止依存 587 本；KST.SConstruction.CubicalLambdaNativeInjectiveNaturality → KST.SConstruction.CubicalLambdaNativeInjectiveComponent |
| R64 | KST.SConstruction.CubicalLambdaNativeNaturality |  禁止依存 598 本；KST.SConstruction.CubicalLambdaNativeNaturality → KST.SConstruction.CubicalLambdaNativeCollapsedHigher |
| R64 | KST.SConstruction.CubicalLambdaNativeNoninjectiveImage |  禁止依存 336 本；KST.SConstruction.CubicalLambdaNativeNoninjectiveImage → KST.SConstruction.CubicalLambdaNativeNormalizedComponent |
| R64 | KST.SConstruction.CubicalLambdaNativeNormalizedComponent |  禁止依存 323 本；KST.SConstruction.CubicalLambdaNativeNormalizedComponent → KST.SConstruction.SimplexSubsetLambdaGeneratorNecklace |
| R64 | KST.SConstruction.CubicalLambdaNativeSimplex |  禁止依存 366 本；KST.SConstruction.CubicalLambdaNativeSimplex → KST.SConstruction.CubicalLambdaNativeDifferentialBoundary |
| R64 | KST.SConstruction.CubicalLambdaNativeSimplexData |  禁止依存 294 本；KST.SConstruction.CubicalLambdaNativeSimplexData → IC.DGNerve.FunctorMapping |
| R64 | KST.SConstruction.CubicalLambdaNerve |  禁止依存 599 本；KST.SConstruction.CubicalLambdaNerve → KST.SConstruction.CubicalLambdaNativeNaturality |
| R64 | KST.SConstruction.CubicalLambdaNerveMap |  禁止依存 600 本；KST.SConstruction.CubicalLambdaNerveMap → KST.SConstruction.CubicalLambdaNerve |
| R64 | KST.SConstruction.CubicalLambdaNerveNativeIso |  禁止依存 600 本；KST.SConstruction.CubicalLambdaNerveNativeIso → KST.SConstruction.CubicalLambdaNerve |
| R64 | KST.SConstruction.CubicalLambdaNerveNativeNaturality |  禁止依存 603 本；KST.SConstruction.CubicalLambdaNerveNativeNaturality → IC.DGNerve.Functor |
| R64 | KST.SConstruction.CubicalLambdaNerveTensor |  禁止依存 602 本；KST.SConstruction.CubicalLambdaNerveTensor → KST.SConstruction.CubicalLambdaFunctorPair |
| R64 | KST.SConstruction.CubicalLambdaNerveUnits |  禁止依存 608 本；KST.SConstruction.CubicalLambdaNerveUnits → KST.SConstruction.CubicalLambdaFunctorPairCoherence |
| R64 | KST.SConstruction.CubicalLambdaOplaxAssociativity |  禁止依存 279 本；KST.SConstruction.CubicalLambdaOplaxAssociativity → KST.SConstruction.CubicalLambdaTriplePair |
| R64 | KST.SConstruction.CubicalLambdaOplaxUnitLaws |  禁止依存 277 本；KST.SConstruction.CubicalLambdaOplaxUnitLaws → KST.SConstruction.ComonoidPairUnit |
| R64 | KST.SConstruction.CubicalLambdaPerfRightActionCoherence |  禁止依存 2081 本；KST.SConstruction.CubicalLambdaPerfRightActionCoherence → KST.SConstruction.CubicalLambdaFunctorPairCoherence |
| R64 | KST.SConstruction.CubicalLambdaPointPair |  禁止依存 572 本；KST.SConstruction.CubicalLambdaPointPair → DifferentialGraded.Category.TensorInclusions |
| R64 | KST.SConstruction.CubicalLambdaTensorMap |  禁止依存 272 本；KST.SConstruction.CubicalLambdaTensorMap → KST.SConstruction.CubicalLambdaDiagonal |
| R64 | KST.SConstruction.CubicalLambdaTensorNaturality |  禁止依存 273 本；KST.SConstruction.CubicalLambdaTensorNaturality → KST.SConstruction.CubicalLambdaTensorMap |
| R64 | KST.SConstruction.CubicalLambdaTriplePair |  禁止依存 277 本；KST.SConstruction.CubicalLambdaTriplePair → KST.SConstruction.ComonoidTriplePair |
| R64 | KST.SConstruction.CubicalPresheaf |  禁止依存 147 本；KST.SConstruction.CubicalPresheaf → KST.SConstruction.SerreConcreteCubeFunctor |
| R64 | KST.SConstruction.CubicalRigidification |  禁止依存 200 本；KST.SConstruction.CubicalRigidification → KST.SConstruction.NecklaceCubicalAssociativity |
| R64 | KST.SConstruction.CubicalSerreAdjunction |  禁止依存 149 本；KST.SConstruction.CubicalSerreAdjunction → KST.SConstruction.CubicalSerreChains |
| R64 | KST.SConstruction.CubicalSerreCellRestriction |  禁止依存 151 本；KST.SConstruction.CubicalSerreCellRestriction → KST.SConstruction.CubicalSerreGenerators |
| R64 | KST.SConstruction.CubicalSerreChains |  禁止依存 148 本；KST.SConstruction.CubicalSerreChains → KST.SConstruction.CubicalPresheaf |
| R64 | KST.SConstruction.CubicalSerreColimit |  禁止依存 149 本；KST.SConstruction.CubicalSerreColimit → KST.SConstruction.CubicalSerreChains |
| R64 | KST.SConstruction.CubicalSerreComonoid |  禁止依存 153 本；KST.SConstruction.CubicalSerreComonoid → KST.SConstruction.ComonoidGeneratorLaws |
| R64 | KST.SConstruction.CubicalSerreComonoidCells |  禁止依存 207 本；KST.SConstruction.CubicalSerreComonoidCells → KST.SConstruction.CubicalSerreDayPair |
| R64 | KST.SConstruction.CubicalSerreDayAssembly |  禁止依存 205 本；KST.SConstruction.CubicalSerreDayAssembly → KST.SConstruction.CubicalSerreDayComparison |
| R64 | KST.SConstruction.CubicalSerreDayAssociativity |  禁止依存 217 本；KST.SConstruction.CubicalSerreDayAssociativity → KST.SConstruction.CubicalSerreDayTripleAssembly |
| R64 | KST.SConstruction.CubicalSerreDayComonoidComparison |  禁止依存 219 本；KST.SConstruction.CubicalSerreDayComonoidComparison → KST.SConstruction.ComonoidGeneratorCompatibility |
| R64 | KST.SConstruction.CubicalSerreDayComonoidMonoidal |  禁止依存 234 本；KST.SConstruction.CubicalSerreDayComonoidMonoidal → KST.SConstruction.ComonoidMonoidalLift |
| R64 | KST.SConstruction.CubicalSerreDayComonoidRecovery |  禁止依存 235 本；KST.SConstruction.CubicalSerreDayComonoidRecovery → KST.SConstruction.CubicalSerreDayComonoidMonoidal |
| R64 | KST.SConstruction.CubicalSerreDayComonoidUnit |  禁止依存 217 本；KST.SConstruction.CubicalSerreDayComonoidUnit → KST.SConstruction.CubicalSerreComonoidCells |
| R64 | KST.SConstruction.CubicalSerreDayComparison |  禁止依存 204 本；KST.SConstruction.CubicalSerreDayComparison → KST.SConstruction.CubicalSerreAdjunction |
| R64 | KST.SConstruction.CubicalSerreDayInverse |  禁止依存 207 本；KST.SConstruction.CubicalSerreDayInverse → KST.SConstruction.CubicalSerreDayAssembly |
| R64 | KST.SConstruction.CubicalSerreDayIso |  禁止依存 212 本；KST.SConstruction.CubicalSerreDayIso → KST.SConstruction.CubicalSerreDayInverse |
| R64 | KST.SConstruction.CubicalSerreDayMonoidal |  禁止依存 223 本；KST.SConstruction.CubicalSerreDayMonoidal → KST.SConstruction.CubicalSerreDayAssociativity |
| R64 | KST.SConstruction.CubicalSerreDayMonoidalRecovery |  禁止依存 224 本；KST.SConstruction.CubicalSerreDayMonoidalRecovery → KST.SConstruction.CubicalSerreDayMonoidal |
| R64 | KST.SConstruction.CubicalSerreDayNaturality |  禁止依存 208 本；KST.SConstruction.CubicalSerreDayNaturality → KST.SConstruction.CubicalDayRepresentableNaturality |
| R64 | KST.SConstruction.CubicalSerreDayPair |  禁止依存 202 本；KST.SConstruction.CubicalSerreDayPair → KST.SConstruction.CubicalDayCells |
| R64 | KST.SConstruction.CubicalSerreDayRepresentable |  禁止依存 209 本；KST.SConstruction.CubicalSerreDayRepresentable → KST.SConstruction.CubicalSerreDayNaturality |
| R64 | KST.SConstruction.CubicalSerreDayTripleAssembly |  禁止依存 216 本；KST.SConstruction.CubicalSerreDayTripleAssembly → KST.SConstruction.CubicalDayStructuralCells |
| R64 | KST.SConstruction.CubicalSerreDayUnit |  禁止依存 212 本；KST.SConstruction.CubicalSerreDayUnit → KST.SConstruction.CubicalDayUnit |
| R64 | KST.SConstruction.CubicalSerreDayUnitCoherence |  禁止依存 219 本；KST.SConstruction.CubicalSerreDayUnitCoherence → KST.SConstruction.CubicalDayStructuralCells |
| R64 | KST.SConstruction.CubicalSerreDiagonal |  禁止依存 151 本；KST.SConstruction.CubicalSerreDiagonal → KST.SConstruction.CubicalSerreGenerators |
| R64 | KST.SConstruction.CubicalSerreGeneratorTensor |  禁止依存 213 本；KST.SConstruction.CubicalSerreGeneratorTensor → KST.SConstruction.CubicalDayRepresentable |
| R64 | KST.SConstruction.CubicalSerreGenerators |  禁止依存 150 本；KST.SConstruction.CubicalSerreGenerators → KST.SConstruction.CubicalSerreColimit |
| R64 | KST.SConstruction.CubicalSerreRepresentable |  禁止依存 154 本；KST.SConstruction.CubicalSerreRepresentable → KST.SConstruction.CubicalSerreComonoid |
| R64 | KST.SConstruction.CubicalSerreTensorColimit |  禁止依存 151 本；KST.SConstruction.CubicalSerreTensorColimit → DifferentialGraded.Complexes.Closed |
| R64 | KST.SConstruction.CubicalSerreTripleColimit |  禁止依存 152 本；KST.SConstruction.CubicalSerreTripleColimit → KST.SConstruction.CubicalSerreTensorColimit |
| R64 | KST.SConstruction.CubicalSerreWhiskerColimit |  禁止依存 152 本；KST.SConstruction.CubicalSerreWhiskerColimit → KST.SConstruction.CubicalSerreTensorColimit |
| R64 | KST.SConstruction.CylinderCellWalks |  禁止依存 74 本；KST.SConstruction.CylinderCellWalks → KST.SConstruction.FamilyHomotopyChains |
| R64 | KST.SConstruction.DoubleCylinderContractibility |  禁止依存 140 本；KST.SConstruction.DoubleCylinderContractibility → HA.Simplicial.MonoRightLiftingContraction |
| R64 | KST.SConstruction.EnrichedFunctorCollage |  禁止依存 791 本；KST.SConstruction.EnrichedFunctorCollage → KST.SConstruction.PointedKanLoopInfinity |
| R64 | KST.SConstruction.EnrichedFunctorCollageNerve |  禁止依存 792 本；KST.SConstruction.EnrichedFunctorCollageNerve → KST.SConstruction.EnrichedFunctorCollage |
| R64 | KST.SConstruction.ExInfinityPointedEnrichedFunctor |  禁止依存 262 本；KST.SConstruction.ExInfinityPointedEnrichedFunctor → KST.Comparison.ExInfinityMonoidal |
| R64 | KST.SConstruction.ExInfinityPointedFamilies |  禁止依存 263 本；KST.SConstruction.ExInfinityPointedFamilies → KST.SConstruction.ExInfinityPointedEnrichedFunctor |
| R64 | KST.SConstruction.ExInfinityPointedUnitWhisker |  禁止依存 267 本；KST.SConstruction.ExInfinityPointedUnitWhisker → KST.SConstruction.ExInfinityPointedFamilies |
| R64 | KST.SConstruction.ExInfinityPointedWeakEquivalence |  禁止依存 283 本；KST.SConstruction.ExInfinityPointedWeakEquivalence → KST.SConstruction.LocalizedPiComparison |
| R64 | KST.SConstruction.ExInfinitySuspensionAssemblyUnit |  禁止依存 271 本；KST.SConstruction.ExInfinitySuspensionAssemblyUnit → KST.SConstruction.CoaugmentedPointedFunctorialMaps |
| R64 | KST.SConstruction.ExInfinitySuspensionComparison |  禁止依存 270 本；KST.SConstruction.ExInfinitySuspensionComparison → KST.SConstruction.CoaugmentedPointedSuspensionNaturality |
| R64 | KST.SConstruction.ExInfinitySuspensionTransformation |  禁止依存 285 本；KST.SConstruction.ExInfinitySuspensionTransformation → KST.SConstruction.CoaugmentedPointedSuspensionTransformation |
| R64 | KST.SConstruction.ExInfinityThenSuspensionHom |  禁止依存 1987 本；KST.SConstruction.ExInfinityThenSuspensionHom → KST.SConstruction.CoaugmentedPointedSuspensionTransformation |
| R64 | KST.SConstruction.FundamentalGroupoidEquivalence |  禁止依存 26 本；KST.SConstruction.FundamentalGroupoidEquivalence → HA.Simplicial.KanHomotopyExtension |
| R64 | KST.SConstruction.FundamentalGroupoidGenerators |  禁止依存 27 本；KST.SConstruction.FundamentalGroupoidGenerators → KST.SConstruction.FundamentalGroupoidEquivalence |
| R64 | KST.SConstruction.FundamentalLoopEdges | 衝突：KST.SConstruction.FundamentalLoopEdges, KST.Spectra.FundamentalLoopEdges |
| R64 | KST.SConstruction.FundamentalLoopHom |  禁止依存 1 本；KST.SConstruction.FundamentalLoopHom → KST.SConstruction.FundamentalLoopEdges |
| R64 | KST.SConstruction.HomotopyEndpointEvaluation |  禁止依存 2 本；KST.SConstruction.HomotopyEndpointEvaluation → IC.Stable.HomotopyEvaluationClass |
| R64 | KST.SConstruction.HomotopySpecifiedVertexCorrection |  禁止依存 45 本；KST.SConstruction.HomotopySpecifiedVertexCorrection → KST.SConstruction.VertexDiscreteHomotopyCorrection |
| R64 | KST.SConstruction.KanMappingCompositionLifting |  禁止依存 73 本；KST.SConstruction.KanMappingCompositionLifting → KST.SConstruction.KanFibrationTriangleLifting |
| R64 | KST.SConstruction.NecklaceBeadRefinement |  禁止依存 166 本；KST.SConstruction.NecklaceBeadRefinement → KST.SConstruction.NecklaceSimplexIntervalTerminal |
| R64 | KST.SConstruction.NecklaceClosedIntervalSubset |  禁止依存 207 本；KST.SConstruction.NecklaceClosedIntervalSubset → KST.SConstruction.NecklaceSimplexSubsetAt |
| R64 | KST.SConstruction.NecklaceConcreteCube |  禁止依存 148 本；KST.SConstruction.NecklaceConcreteCube → KST.SConstruction.CubicalPresheaf |
| R64 | KST.SConstruction.NecklaceCubeMonoidal |  禁止依存 171 本；KST.SConstruction.NecklaceCubeMonoidal → KST.SConstruction.NecklaceCubeMonoidalCoherence |
| R64 | KST.SConstruction.NecklaceCubeMonoidalCoherence |  禁止依存 170 本；KST.SConstruction.NecklaceCubeMonoidalCoherence → KST.SConstruction.ConcreteCubeMonoidal |
| R64 | KST.SConstruction.NecklaceCubeTensorComparison |  禁止依存 165 本；KST.SConstruction.NecklaceCubeTensorComparison → KST.SConstruction.ConcreteCubeDimensionIso |
| R64 | KST.SConstruction.NecklaceCubicalAssociativity |  禁止依存 197 本；KST.SConstruction.NecklaceCubicalAssociativity → KST.SConstruction.NecklaceCubicalTripleExt |
| R64 | KST.SConstruction.NecklaceCubicalComposeCell |  禁止依存 176 本；KST.SConstruction.NecklaceCubicalComposeCell → KST.SConstruction.NecklaceCubicalMapping |
| R64 | KST.SConstruction.NecklaceCubicalComposition |  禁止依存 181 本；KST.SConstruction.NecklaceCubicalComposition → KST.SConstruction.CubicalDayBicolimit |
| R64 | KST.SConstruction.NecklaceCubicalCompositionNaturality |  禁止依存 183 本；KST.SConstruction.NecklaceCubicalCompositionNaturality → KST.SConstruction.NecklaceCubicalComposition |
| R64 | KST.SConstruction.NecklaceCubicalDayData |  禁止依存 195 本；KST.SConstruction.NecklaceCubicalDayData → KST.SConstruction.CubicalDayWrappedColimits |
| R64 | KST.SConstruction.NecklaceCubicalIdentity |  禁止依存 187 本；KST.SConstruction.NecklaceCubicalIdentity → KST.SConstruction.NecklaceCubicalMapping |
| R64 | KST.SConstruction.NecklaceCubicalMapping |  禁止依存 149 本；KST.SConstruction.NecklaceCubicalMapping → KST.SConstruction.NecklaceConcreteCube |
| R64 | KST.SConstruction.NecklaceCubicalMonoidal |  禁止依存 184 本；KST.SConstruction.NecklaceCubicalMonoidal → KST.SConstruction.CubicalDayYonedaMonoidal |
| R64 | KST.SConstruction.NecklaceCubicalPostcomposition |  禁止依存 150 本；KST.SConstruction.NecklaceCubicalPostcomposition → KST.SConstruction.NecklaceCubicalMapping |
| R64 | KST.SConstruction.NecklaceCubicalTensorComparison |  禁止依存 174 本；KST.SConstruction.NecklaceCubicalTensorComparison → KST.SConstruction.CubicalDayRepresentableNaturality |
| R64 | KST.SConstruction.NecklaceCubicalTripleExt |  禁止依存 196 本；KST.SConstruction.NecklaceCubicalTripleExt → KST.SConstruction.NecklaceCubicalDayData |
| R64 | KST.SConstruction.NecklaceCubicalUnitLaws |  禁止依存 196 本；KST.SConstruction.NecklaceCubicalUnitLaws → KST.SConstruction.NecklaceCubicalDayData |
| R64 | KST.SConstruction.NecklaceIsoCubicalMapping |  禁止依存 150 本；KST.SConstruction.NecklaceIsoCubicalMapping → KST.SConstruction.NecklaceCubicalMapping |
| R64 | KST.SConstruction.NecklaceLambdaCell |  禁止依存 268 本；KST.SConstruction.NecklaceLambdaCell → KST.SConstruction.CubicalLambdaComonoids |
| R64 | KST.SConstruction.NecklaceLambdaCellPostcomposition |  禁止依存 269 本；KST.SConstruction.NecklaceLambdaCellPostcomposition → KST.SConstruction.NecklaceCubicalPostcomposition |
| R64 | KST.SConstruction.NecklaceLambdaComposition |  禁止依存 270 本；KST.SConstruction.NecklaceLambdaComposition → KST.SConstruction.CubicalSerreComonoidCells |
| R64 | KST.SConstruction.NecklaceLambdaMappedTop |  禁止依存 283 本；KST.SConstruction.NecklaceLambdaMappedTop → KST.SConstruction.NecklaceLambdaComposition |
| R64 | KST.SConstruction.NecklaceLambdaTopComposition |  禁止依存 282 本；KST.SConstruction.NecklaceLambdaTopComposition → KST.SConstruction.NecklaceLambdaComposition |
| R64 | KST.SConstruction.NecklaceNumericCubeComparison |  禁止依存 149 本；KST.SConstruction.NecklaceNumericCubeComparison → KST.SConstruction.NecklaceConcreteCube |
| R64 | KST.SConstruction.NecklaceRefinementCoordinates |  禁止依存 172 本；KST.SConstruction.NecklaceRefinementCoordinates → KST.SConstruction.NecklaceRefinementNonjoint |
| R64 | KST.SConstruction.NecklaceRefinementInSimplex |  禁止依存 167 本；KST.SConstruction.NecklaceRefinementInSimplex → KST.SConstruction.NecklaceBeadRefinement |
| R64 | KST.SConstruction.NecklaceRefinementLambdaCell |  禁止依存 284 本；KST.SConstruction.NecklaceRefinementLambdaCell → KST.SConstruction.NecklaceRefinementInSimplex |
| R64 | KST.SConstruction.NecklaceRefinementMissingCoordinate |  禁止依存 173 本；KST.SConstruction.NecklaceRefinementMissingCoordinate → KST.SConstruction.NecklaceRefinementCoordinates |
| R64 | KST.SConstruction.NecklaceRefinementNonjoint |  禁止依存 167 本；KST.SConstruction.NecklaceRefinementNonjoint → KST.SConstruction.NecklaceBeadRefinement |
| R64 | KST.SConstruction.NecklaceRefinementOneFace |  禁止依存 181 本；KST.SConstruction.NecklaceRefinementOneFace → KST.SConstruction.ConcreteCubeFaceCriterion |
| R64 | KST.SConstruction.NecklaceSimplexIntervalTerminal |  禁止依存 165 本；KST.SConstruction.NecklaceSimplexIntervalTerminal → KST.SConstruction.SimplexBeadCubicalMapping |
| R64 | KST.SConstruction.NecklaceSimplexSubset |  禁止依存 166 本；KST.SConstruction.NecklaceSimplexSubset → KST.SConstruction.NecklaceSimplexIntervalTerminal |
| R64 | KST.SConstruction.NecklaceSimplexSubsetAt |  禁止依存 168 本；KST.SConstruction.NecklaceSimplexSubsetAt → KST.SConstruction.NecklaceCubicalMapping |
| R64 | KST.SConstruction.NecklaceSimplexSubsetErase |  禁止依存 172 本；KST.SConstruction.NecklaceSimplexSubsetErase → IC.DGNerve.Index |
| R64 | KST.SConstruction.NecklaceSimplexSubsetImage |  禁止依存 207 本；KST.SConstruction.NecklaceSimplexSubsetImage → KST.SConstruction.NecklaceSimplexSubsetAt |
| R64 | KST.SConstruction.NecklaceSimplexSubsetImageFactor |  禁止依存 172 本；KST.SConstruction.NecklaceSimplexSubsetImageFactor → KST.SConstruction.NecklaceSimplexSubsetAt |
| R64 | KST.SConstruction.NecklaceSimplexSubsetInclusion |  禁止依存 167 本；KST.SConstruction.NecklaceSimplexSubsetInclusion → KST.SConstruction.NecklaceSimplexSubset |
| R64 | KST.SConstruction.NecklaceSingleCoordinateValue |  禁止依存 183 本；KST.SConstruction.NecklaceSingleCoordinateValue → KST.SConstruction.NecklaceWedgeBeadOneFace |
| R64 | KST.SConstruction.NecklaceWedgeBeadOneFace |  禁止依存 182 本；KST.SConstruction.NecklaceWedgeBeadOneFace → KST.SConstruction.NecklaceRefinementOneFace |
| R64 | KST.SConstruction.NecklaceWedgeNumericJoin |  禁止依存 155 本；KST.SConstruction.NecklaceWedgeNumericJoin → KST.SConstruction.CubeVertexBlockCoordinates |
| R64 | KST.SConstruction.NecklaceWedgeNumericMap |  禁止依存 156 本；KST.SConstruction.NecklaceWedgeNumericMap → KST.SConstruction.NecklaceWedgeNumericJoin |
| R64 | KST.SConstruction.PathBoundaryCartesian |  禁止依存 1020 本；KST.SConstruction.PathBoundaryCartesian → KST.SConstruction.PathFirstFaceHomotopyPullback |
| R64 | KST.SConstruction.PathBoundaryRealizationPullback |  禁止依存 1126 本；KST.SConstruction.PathBoundaryRealizationPullback → KST.Comparison.SegalRealizationComparison |
| R64 | KST.SConstruction.PathContractionAssembly |  禁止依存 225 本；KST.SConstruction.PathContractionAssembly → KST.SConstruction.DiagonalAssembly |
| R64 | KST.SConstruction.PathContractionSection |  禁止依存 226 本；KST.SConstruction.PathContractionSection → KST.SConstruction.PathContractionAssembly |
| R64 | KST.SConstruction.PathFirstFaceHomotopyPullback |  禁止依存 1014 本；KST.SConstruction.PathFirstFaceHomotopyPullback → KST.SConstruction.ConnectedDiagramRetractions |
| R64 | KST.SConstruction.PathFirstRow |  禁止依存 352 本；KST.SConstruction.PathFirstRow → HA.Simplicial.DiagonalLocalizedEquivalence |
| R64 | KST.SConstruction.PathFirstRowNaturality |  禁止依存 458 本；KST.SConstruction.PathFirstRowNaturality → KST.SConstruction.CofiberPostcompLaws |
| R64 | KST.SConstruction.PathHeadHomotopyPullback |  禁止依存 924 本；KST.SConstruction.PathHeadHomotopyPullback → KST.Comparison.HomotopyPullbackSymmetry |
| R64 | KST.SConstruction.PathHeadSegalComparison |  禁止依存 803 本；KST.SConstruction.PathHeadSegalComparison → KST.SConstruction.EdgeSegalEquivalence |
| R64 | KST.SConstruction.PathHomotopyFiberFunctor |  禁止依存 123 本；KST.SConstruction.PathHomotopyFiberFunctor → KST.SConstruction.PathHomotopyFiberNaturality |
| R64 | KST.SConstruction.PathHomotopyFiberNaturality |  禁止依存 122 本；KST.SConstruction.PathHomotopyFiberNaturality → KST.SConstruction.LoopHomotopyFiber |
| R64 | KST.SConstruction.PathZeroColumnSection |  禁止依存 1142 本；KST.SConstruction.PathZeroColumnSection → KST.SConstruction.ZeroRowPathFiberComparison |
| R64 | KST.SConstruction.Pointed |  禁止依存 97 本；KST.SConstruction.Pointed → KST.SConstruction.DegeneratePushouts |
| R64 | KST.SConstruction.PointedArrowEvaluation |  禁止依存 543 本；KST.SConstruction.PointedArrowEvaluation → KST.SConstruction.InverseMixedFamilyTransport |
| R64 | KST.SConstruction.PointedArrowIdentityTransport |  禁止依存 135 本；KST.SConstruction.PointedArrowIdentityTransport → KST.SConstruction.AssemblyArrowIdentityLegs |
| R64 | KST.SConstruction.PointedBasedActionFunctor |  禁止依存 150 本；KST.SConstruction.PointedBasedActionFunctor → KST.SConstruction.PointedEnrichedActionFunctor |
| R64 | KST.SConstruction.PointedChoiceBaseIso |  禁止依存 123 本；KST.SConstruction.PointedChoiceBaseIso → KST.SConstruction.PointedExtensionSpace |
| R64 | KST.SConstruction.PointedClosedEvaluation |  禁止依存 145 本；KST.SConstruction.PointedClosedEvaluation → KST.SConstruction.PointedClosedHomInclusion |
| R64 | KST.SConstruction.PointedClosedHomInclusion |  禁止依存 144 本；KST.SConstruction.PointedClosedHomInclusion → KST.SConstruction.LaxClosedFamilyMap |
| R64 | KST.SConstruction.PointedCompatibilityInterchange |  禁止依存 168 本；KST.SConstruction.PointedCompatibilityInterchange → KST.SConstruction.FamilyChainInterchangeSquares |
| R64 | KST.SConstruction.PointedComponentAdjointSquare |  禁止依存 526 本；KST.SConstruction.PointedComponentAdjointSquare → KST.SConstruction.BoundaryAssemblyNaturality |
| R64 | KST.SConstruction.PointedComponentAssemblyTransfer |  禁止依存 121 本；KST.SConstruction.PointedComponentAssemblyTransfer → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.SConstruction.PointedComponentNaturalSquare |  禁止依存 121 本；KST.SConstruction.PointedComponentNaturalSquare → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.SConstruction.PointedComponentPiIsomorphism |  禁止依存 134 本；KST.SConstruction.PointedComponentPiIsomorphism → KST.SConstruction.LocalizedPiComparison |
| R64 | KST.SConstruction.PointedComponentSquareComposition |  禁止依存 121 本；KST.SConstruction.PointedComponentSquareComposition → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.SConstruction.PointedCompositeCorrectionChains |  禁止依存 165 本；KST.SConstruction.PointedCompositeCorrectionChains → KST.SConstruction.FamilyChainPairing |
| R64 | KST.SConstruction.PointedCompositionProjection |  禁止依存 752 本；KST.SConstruction.PointedCompositionProjection → KST.SConstruction.SpectrumFixedFactorEvaluation |
| R64 | KST.SConstruction.PointedContractibility |  禁止依存 112 本；KST.SConstruction.PointedContractibility → KST.SConstruction.LocalizedPiComparison |
| R64 | KST.SConstruction.PointedCoreSimplicial |  禁止依存 155 本；KST.SConstruction.PointedCoreSimplicial → KST.SConstruction.CoreSimplicial |
| R64 | KST.SConstruction.PointedCorrectionInterchange |  禁止依存 395 本；KST.SConstruction.PointedCorrectionInterchange → KST.SConstruction.EdgeFamilyCylinders |
| R64 | KST.SConstruction.PointedCylinderOmegaCriterion |  禁止依存 141 本；KST.SConstruction.PointedCylinderOmegaCriterion → KST.SConstruction.PointedComponentPiIsomorphism |
| R64 | KST.SConstruction.PointedDoubleMappingCylinderMono |  禁止依存 1972 本；KST.SConstruction.PointedDoubleMappingCylinderMono → KST.SConstruction.PointedTensorMappingCylinderMono |
| R64 | KST.SConstruction.PointedDoubleMappingCylinderWeakEquivalence |  禁止依存 1980 本；KST.SConstruction.PointedDoubleMappingCylinderWeakEquivalence → KST.SConstruction.PointedPushoutLocalizedMono |
| R64 | KST.SConstruction.PointedEnrichedActionFunctor |  禁止依存 149 本；KST.SConstruction.PointedEnrichedActionFunctor → KST.SConstruction.InternalEnrichedActionFunctor |
| R64 | KST.SConstruction.PointedEnrichedCylinderCompletion |  禁止依存 1996 本；KST.SConstruction.PointedEnrichedCylinderCompletion → KST.SConstruction.ExInfinityPointedUnitWhisker |
| R64 | KST.SConstruction.PointedEnrichedCylinderCompletionNaturality |  禁止依存 1997 本；KST.SConstruction.PointedEnrichedCylinderCompletionNaturality → KST.SConstruction.PointedEnrichedCylinderCompletion |
| R64 | KST.SConstruction.PointedEnrichedCylinderCompletionProperties |  禁止依存 2021 本；KST.SConstruction.PointedEnrichedCylinderCompletionProperties → KST.SConstruction.PointedEnrichedCylinderCompletion |
| R64 | KST.SConstruction.PointedEnrichedCylinderComponents |  禁止依存 2001 本；KST.SConstruction.PointedEnrichedCylinderComponents → KST.SConstruction.PointedEnrichedCylinderCompletion |
| R64 | KST.SConstruction.PointedEnrichedCylinderPushout |  禁止依存 1982 本；KST.SConstruction.PointedEnrichedCylinderPushout → KST.SConstruction.PointedEnrichedMappingCylinderNaturality |
| R64 | KST.SConstruction.PointedEnrichedCylinderPushoutNaturality |  禁止依存 1983 本；KST.SConstruction.PointedEnrichedCylinderPushoutNaturality → KST.SConstruction.EnrichedWhiskerNaturality |
| R64 | KST.SConstruction.PointedEnrichedCylinderPushoutProperties |  禁止依存 2006 本；KST.SConstruction.PointedEnrichedCylinderPushoutProperties → KST.SConstruction.PointedDoubleMappingCylinderMono |
| R64 | KST.SConstruction.PointedEnrichedKanLift |  禁止依存 195 本；KST.SConstruction.PointedEnrichedKanLift → KST.SConstruction.PointedKanEnrichedObjects |
| R64 | KST.SConstruction.PointedEnrichedMappingCylinder |  禁止依存 1976 本；KST.SConstruction.PointedEnrichedMappingCylinder → KST.SConstruction.PointedEnrichedSpanFunctor |
| R64 | KST.SConstruction.PointedEnrichedMappingCylinderComponents |  禁止依存 1978 本；KST.SConstruction.PointedEnrichedMappingCylinderComponents → KST.SConstruction.PointedEnrichedMappingCylinder |
| R64 | KST.SConstruction.PointedEnrichedMappingCylinderNaturality |  禁止依存 1981 本；KST.SConstruction.PointedEnrichedMappingCylinderNaturality → KST.SConstruction.PointedEnrichedMappingCylinderComponents |
| R64 | KST.SConstruction.PointedEnrichedMappingCylinderTransformations |  禁止依存 1982 本；KST.SConstruction.PointedEnrichedMappingCylinderTransformations → KST.SConstruction.PointedEnrichedMappingCylinderNaturality |
| R64 | KST.SConstruction.PointedEnrichedMonicReplacement |  禁止依存 1994 本；KST.SConstruction.PointedEnrichedMonicReplacement → KST.SConstruction.ExInfinityPointedUnitWhisker |
| R64 | KST.SConstruction.PointedEnrichedMonicReplacementNaturality |  禁止依存 1995 本；KST.SConstruction.PointedEnrichedMonicReplacementNaturality → KST.SConstruction.PointedEnrichedMonicReplacement |
| R64 | KST.SConstruction.PointedEnrichedMonicReplacementProperties |  禁止依存 2017 本；KST.SConstruction.PointedEnrichedMonicReplacementProperties → KST.SConstruction.PointedDoubleMappingCylinderWeakEquivalence |
| R64 | KST.SConstruction.PointedEnrichedMonicReplacementTransformations |  禁止依存 1996 本；KST.SConstruction.PointedEnrichedMonicReplacementTransformations → KST.SConstruction.PointedEnrichedMonicReplacementNaturality |
| R64 | KST.SConstruction.PointedEnrichedSpanFunctor |  禁止依存 148 本；KST.SConstruction.PointedEnrichedSpanFunctor → KST.SConstruction.PointedSpanEnrichment |
| R64 | KST.SConstruction.PointedExtensionArrowDiagram |  禁止依存 124 本；KST.SConstruction.PointedExtensionArrowDiagram → KST.SConstruction.AssemblyInputArrows |
| R64 | KST.SConstruction.PointedExtensionHomotopy |  禁止依存 119 本；KST.SConstruction.PointedExtensionHomotopy → KST.SConstruction.PointedExtensionSpace |
| R64 | KST.SConstruction.PointedExtensionSpace |  禁止依存 117 本；KST.SConstruction.PointedExtensionSpace → KST.Spectra.FreePathSpace |
| R64 | KST.SConstruction.PointedExtensionTransport |  禁止依存 121 本；KST.SConstruction.PointedExtensionTransport → KST.SConstruction.PointedExtensionHomotopy |
| R64 | KST.SConstruction.PointedExtensionTransportLaws |  禁止依存 122 本；KST.SConstruction.PointedExtensionTransportLaws → KST.SConstruction.PointedExtensionTransport |
| R64 | KST.SConstruction.PointedFamilyConstantComposition |  禁止依存 121 本；KST.SConstruction.PointedFamilyConstantComposition → KST.Spectra.PointedEnrichment |
| R64 | KST.SConstruction.PointedFamilyPost |  禁止依存 146 本；KST.SConstruction.PointedFamilyPost → KST.SConstruction.PointedClosedEvaluation |
| R64 | KST.SConstruction.PointedFamilyWhiskerNaturality |  禁止依存 150 本；KST.SConstruction.PointedFamilyWhiskerNaturality → KST.SConstruction.PointedSSetWhisker |
| R64 | KST.SConstruction.PointedFixedVertexComposition |  禁止依存 122 本；KST.SConstruction.PointedFixedVertexComposition → KST.SConstruction.PointedFamilyConstantComposition |
| R64 | KST.SConstruction.PointedFreeFamily |  禁止依存 147 本；KST.SConstruction.PointedFreeFamily → KST.SConstruction.PointedSSetObject |
| R64 | KST.SConstruction.PointedFullPathBoundary |  禁止依存 500 本；KST.SConstruction.PointedFullPathBoundary → KST.SConstruction.CanonicalIteratedPathBoundary |
| R64 | KST.SConstruction.PointedIteratedPath |  禁止依存 478 本；KST.SConstruction.PointedIteratedPath → KST.SConstruction.PointedContractibility |
| R64 | KST.SConstruction.PointedKanDiagramComponentEquivalences |  禁止依存 755 本；KST.SConstruction.PointedKanDiagramComponentEquivalences → KST.SConstruction.PointedKanHomotopyComponents |
| R64 | KST.SConstruction.PointedKanDiagramEquivalences |  禁止依存 753 本；KST.SConstruction.PointedKanDiagramEquivalences → KST.SConstruction.PointedKanEnrichedEquivalences |
| R64 | KST.SConstruction.PointedKanDiagramExtensionComponents |  禁止依存 786 本；KST.SConstruction.PointedKanDiagramExtensionComponents → KST.SConstruction.PointedExtensionHomotopy |
| R64 | KST.SConstruction.PointedKanDiagramExtensions |  禁止依存 759 本；KST.SConstruction.PointedKanDiagramExtensions → IC.F1B.FunctorCategories.FunctorHomotopyComposition |
| R64 | KST.SConstruction.PointedKanDiagramInverseTriangles |  禁止依存 775 本；KST.SConstruction.PointedKanDiagramInverseTriangles → IC.F1B.Homotopy.HomotopyWhiskering |
| R64 | KST.SConstruction.PointedKanDiagramTriangleComponents |  禁止依存 760 本；KST.SConstruction.PointedKanDiagramTriangleComponents → IC.F1.Transport.PointFunctorEvaluation |
| R64 | KST.SConstruction.PointedKanEnrichedEquivalences |  禁止依存 751 本；KST.SConstruction.PointedKanEnrichedEquivalences → IC.F1.Coherent.EnrichedHomotopy |
| R64 | KST.SConstruction.PointedKanEnrichedObjects |  禁止依存 159 本；KST.SConstruction.PointedKanEnrichedObjects → IC.Coherent.Quasicategory |
| R64 | KST.SConstruction.PointedKanHomotopyCategoryComparison |  禁止依存 752 本；KST.SConstruction.PointedKanHomotopyCategoryComparison → IC.F1.Coherent.HomEquivalence |
| R64 | KST.SConstruction.PointedKanHomotopyComponents |  禁止依存 754 本；KST.SConstruction.PointedKanHomotopyComponents → IC.F1.Coherent.EdgeEquiv |
| R64 | KST.SConstruction.PointedKanLoopInfinity |  禁止依存 790 本；KST.SConstruction.PointedKanLoopInfinity → IC.HomotopyLimits.StrictConeFunctorImage |
| R64 | KST.SConstruction.PointedKanReplacementComponents |  禁止依存 284 本；KST.SConstruction.PointedKanReplacementComponents → KST.SConstruction.PointedSOAExInfinityComparison |
| R64 | KST.SConstruction.PointedKanSpecifiedComponentCorrection |  禁止依存 775 本；KST.SConstruction.PointedKanSpecifiedComponentCorrection → KST.SConstruction.HomotopySpecifiedVertexCorrection |
| R64 | KST.SConstruction.PointedKanStrictExtension |  禁止依存 105 本；KST.SConstruction.PointedKanStrictExtension → KST.SConstruction.LocalizedPiComparison |
| R64 | KST.SConstruction.PointedLiftArrowDiagram |  禁止依存 130 本；KST.SConstruction.PointedLiftArrowDiagram → KST.SConstruction.AssemblyInputArrows |
| R64 | KST.SConstruction.PointedLiftSpace |  禁止依存 122 本；KST.SConstruction.PointedLiftSpace → KST.SConstruction.PointedExtensionSpace |
| R64 | KST.SConstruction.PointedLiftTransport |  禁止依存 127 本；KST.SConstruction.PointedLiftTransport → KST.SConstruction.PointedExtensionTransport |
| R64 | KST.SConstruction.PointedLiftTransportLaws |  禁止依存 128 本；KST.SConstruction.PointedLiftTransportLaws → KST.SConstruction.PointedLiftTransport |
| R64 | KST.SConstruction.PointedLoopEnrichment |  禁止依存 38 本；KST.SConstruction.PointedLoopEnrichment → KST.Spectra.PointedEnrichment |
| R64 | KST.SConstruction.PointedMappingCompositionFamilies |  禁止依存 121 本；KST.SConstruction.PointedMappingCompositionFamilies → KST.Spectra.PointedEnrichment |
| R64 | KST.SConstruction.PointedMappingCylinderComponents |  禁止依存 1961 本；KST.SConstruction.PointedMappingCylinderComponents → KST.SConstruction.PointedTensorCylinderHomotopy |
| R64 | KST.SConstruction.PointedMappingLocalizedImage |  禁止依存 121 本；KST.SConstruction.PointedMappingLocalizedImage → HA.Simplicial.AnodyneHomotopyLocalization |
| R64 | KST.SConstruction.PointedMappingPathSections |  禁止依存 123 本；KST.SConstruction.PointedMappingPathSections → KST.SConstruction.PointedLiftSpace |
| R64 | KST.SConstruction.PointedMappingSourceWhiskers |  禁止依存 67 本；KST.SConstruction.PointedMappingSourceWhiskers → KST.Spectra.PointedCofiberMappingNaturality |
| R64 | KST.SConstruction.PointedMappingTransportUnits |  禁止依存 122 本；KST.SConstruction.PointedMappingTransportUnits → KST.SConstruction.PointedExtensionTransport |
| R64 | KST.SConstruction.PointedNaturalityCompositionEdges |  禁止依存 117 本；KST.SConstruction.PointedNaturalityCompositionEdges → KST.Spectra.PointedMappingFamilyVertices |
| R64 | KST.SConstruction.PointedPathComparison |  禁止依存 259 本；KST.SConstruction.PointedPathComparison → KST.SConstruction.KSpace |
| R64 | KST.SConstruction.PointedPiLocalized |  禁止依存 122 本；KST.SConstruction.PointedPiLocalized → KST.SConstruction.LocalizedPiComparison |
| R64 | KST.SConstruction.PointedPostcomposition |  禁止依存 249 本；KST.SConstruction.PointedPostcomposition → KST.SConstruction.KSpace |
| R64 | KST.SConstruction.PointedPullbackFiber |  禁止依存 96 本；KST.SConstruction.PointedPullbackFiber → KST.Spectra.PointedFiber |
| R64 | KST.SConstruction.PointedPushoutAnodyne |  禁止依存 147 本；KST.SConstruction.PointedPushoutAnodyne → KST.SConstruction.PointedSSetObject |
| R64 | KST.SConstruction.PointedPushoutFamily |  禁止依存 149 本；KST.SConstruction.PointedPushoutFamily → KST.SConstruction.ClosedPushoutHom |
| R64 | KST.SConstruction.PointedPushoutLocalizedMono |  禁止依存 161 本；KST.SConstruction.PointedPushoutLocalizedMono → HA.Simplicial.KanTestLiftingClass |
| R64 | KST.SConstruction.PointedPushoutMonomorphism |  禁止依存 147 本；KST.SConstruction.PointedPushoutMonomorphism → HA.Simplicial.Generators |
| R64 | KST.SConstruction.PointedSOAExInfinityComparison |  禁止依存 282 本；KST.SConstruction.PointedSOAExInfinityComparison → KST.SConstruction.ExInfinityPointedEnrichedFunctor |
| R64 | KST.SConstruction.PointedSSetObject |  禁止依存 146 本；KST.SConstruction.PointedSSetObject → KST.SConstruction.PointedClosedHomInclusion |
| R64 | KST.SConstruction.PointedSSetSuspensionFunctor |  禁止依存 162 本；KST.SConstruction.PointedSSetSuspensionFunctor → KST.SConstruction.CoaugmentedPointedSuspensionNaturality |
| R64 | KST.SConstruction.PointedSSetSuspensionHom |  禁止依存 1970 本；KST.SConstruction.PointedSSetSuspensionHom → KST.SConstruction.PointedSSetSuspensionFunctor |
| R64 | KST.SConstruction.PointedSSetWhisker |  禁止依存 149 本；KST.SConstruction.PointedSSetWhisker → KST.SConstruction.PointedFamilyPost |
| R64 | KST.SConstruction.PointedSmashAnodyne |  禁止依存 150 本；KST.SConstruction.PointedSmashAnodyne → KST.SConstruction.PointedSmashPushoutAnodyne |
| R64 | KST.SConstruction.PointedSmashPushoutAnodyne |  禁止依存 149 本；KST.SConstruction.PointedSmashPushoutAnodyne → KST.SConstruction.PointedPushoutAnodyne |
| R64 | KST.SConstruction.PointedSpanEnrichment |  禁止依存 147 本；KST.SConstruction.PointedSpanEnrichment → KST.SConstruction.PointedSSetObject |
| R64 | KST.SConstruction.PointedSpanEvaluationFunctor |  禁止依存 148 本；KST.SConstruction.PointedSpanEvaluationFunctor → KST.SConstruction.PointedSpanEnrichment |
| R64 | KST.SConstruction.PointedSpanPushout |  禁止依存 154 本；KST.SConstruction.PointedSpanPushout → KST.SConstruction.PointedPushoutFamily |
| R64 | KST.SConstruction.PointedSpanPushoutDesc |  禁止依存 160 本；KST.SConstruction.PointedSpanPushoutDesc → KST.SConstruction.PointedSpanPushoutEnrichedFunctor |
| R64 | KST.SConstruction.PointedSpanPushoutDescNaturality |  禁止依存 162 本；KST.SConstruction.PointedSpanPushoutDescNaturality → KST.SConstruction.EnrichedWhiskerNaturality |
| R64 | KST.SConstruction.PointedSpanPushoutEnrichedFunctor |  禁止依存 159 本；KST.SConstruction.PointedSpanPushoutEnrichedFunctor → KST.SConstruction.PointedSpanEvaluationFunctor |
| R64 | KST.SConstruction.PointedSpanPushoutHom |  禁止依存 156 本；KST.SConstruction.PointedSpanPushoutHom → KST.SConstruction.EnrichedCoconeFamily |
| R64 | KST.SConstruction.PointedSpanPushoutMap |  禁止依存 160 本；KST.SConstruction.PointedSpanPushoutMap → KST.SConstruction.PointedSpanPushoutEnrichedFunctor |
| R64 | KST.SConstruction.PointedStandardLoop |  禁止依存 148 本；KST.SConstruction.PointedStandardLoop → KST.SConstruction.PointedLoopEnrichment |
| R64 | KST.SConstruction.PointedStandardLoopEvaluation |  禁止依存 1961 本；KST.SConstruction.PointedStandardLoopEvaluation → KST.SConstruction.PointedSSetWhisker |
| R64 | KST.SConstruction.PointedStrictTransformationOfAction |  禁止依存 150 本；KST.SConstruction.PointedStrictTransformationOfAction → KST.SConstruction.PointedSSetWhisker |
| R64 | KST.SConstruction.PointedSuspensionCoherentDiagram |  禁止依存 1948 本；KST.SConstruction.PointedSuspensionCoherentDiagram → IC.F1.Weighted.CosliceTransport |
| R64 | KST.SConstruction.PointedSuspensionEvaluation |  禁止依存 146 本；KST.SConstruction.PointedSuspensionEvaluation → KST.SConstruction.PointedClosedEvaluation |
| R64 | KST.SConstruction.PointedTensorComparison |  禁止依存 1957 本；KST.SConstruction.PointedTensorComparison → KST.SConstruction.PointedTensorEnrichedFunctor |
| R64 | KST.SConstruction.PointedTensorCylinder |  禁止依存 1957 本；KST.SConstruction.PointedTensorCylinder → KST.SConstruction.PointedTensorEnrichedFunctor |
| R64 | KST.SConstruction.PointedTensorCylinderAnodyne |  禁止依存 1971 本；KST.SConstruction.PointedTensorCylinderAnodyne → KST.SConstruction.PointedSmashAnodyne |
| R64 | KST.SConstruction.PointedTensorCylinderBoundary |  禁止依存 1966 本；KST.SConstruction.PointedTensorCylinderBoundary → IC.HomotopyLimits.SmashMonomorphisms |
| R64 | KST.SConstruction.PointedTensorCylinderBoundaryMono |  禁止依存 1967 本；KST.SConstruction.PointedTensorCylinderBoundaryMono → KST.SConstruction.PointedTensorCylinderBoundary |
| R64 | KST.SConstruction.PointedTensorCylinderCurry |  禁止依存 1958 本；KST.SConstruction.PointedTensorCylinderCurry → KST.SConstruction.PointedTensorCylinder |
| R64 | KST.SConstruction.PointedTensorCylinderHomotopy |  禁止依存 1959 本；KST.SConstruction.PointedTensorCylinderHomotopy → KST.SConstruction.PointedTensorCylinderCurry |
| R64 | KST.SConstruction.PointedTensorCylinderNaturality |  禁止依存 1964 本；KST.SConstruction.PointedTensorCylinderNaturality → KST.SConstruction.PointedTensorCylinderTransformation |
| R64 | KST.SConstruction.PointedTensorCylinderTransformation |  禁止依存 1963 本；KST.SConstruction.PointedTensorCylinderTransformation → KST.SConstruction.PointedTensorCylinder |
| R64 | KST.SConstruction.PointedTensorEnrichedFunctor |  禁止依存 1956 本；KST.SConstruction.PointedTensorEnrichedFunctor → KST.SConstruction.ClosedTensorMappingLaws |
| R64 | KST.SConstruction.PointedTensorMappingCylinder |  禁止依存 1958 本；KST.SConstruction.PointedTensorMappingCylinder → KST.SConstruction.PointedTensorCylinder |
| R64 | KST.SConstruction.PointedTensorMappingCylinderFunctor |  禁止依存 1967 本；KST.SConstruction.PointedTensorMappingCylinderFunctor → KST.SConstruction.PointedTensorMappingCylinderMap |
| R64 | KST.SConstruction.PointedTensorMappingCylinderMap |  禁止依存 1966 本；KST.SConstruction.PointedTensorMappingCylinderMap → KST.SConstruction.PointedTensorCylinderNaturality |
| R64 | KST.SConstruction.PointedTensorMappingCylinderMono |  禁止依存 1971 本；KST.SConstruction.PointedTensorMappingCylinderMono → KST.SConstruction.CoproductPushoutAttachment |
| R64 | KST.SConstruction.PointedTensorMappingCylinderWeakEquivalence |  禁止依存 1974 本；KST.SConstruction.PointedTensorMappingCylinderWeakEquivalence → KST.SConstruction.PointedMappingLocalizedImage |
| R64 | KST.SConstruction.PointedTensorTransformations |  禁止依存 1961 本；KST.SConstruction.PointedTensorTransformations → KST.SConstruction.ClosedTensorMappingUnit |
| R64 | KST.SConstruction.PointedWeakComparisonSquare |  禁止依存 123 本；KST.SConstruction.PointedWeakComparisonSquare → KST.SConstruction.LocalizedPiComparison |
| R64 | KST.SConstruction.SimplexHABeadTailCells |  禁止依存 305 本；KST.SConstruction.SimplexHABeadTailCells → KST.SConstruction.SimplexHABeadWordTransport |
| R64 | KST.SConstruction.SimplexHABeadTailComparison |  禁止依存 307 本；KST.SConstruction.SimplexHABeadTailComparison → KST.SConstruction.SimplexHABeadTailCells |
| R64 | KST.SConstruction.SimplexHABeadTailValues |  禁止依存 301 本；KST.SConstruction.SimplexHABeadTailValues → KST.SConstruction.SimplexHABeadWordTransport |
| R64 | KST.SConstruction.SimplexHABeadWordBoundary |  禁止依存 307 本；KST.SConstruction.SimplexHABeadWordBoundary → KST.SConstruction.SimplexHARawWordComposition |
| R64 | KST.SConstruction.SimplexHABeadWordBoundaryZero |  禁止依存 308 本；KST.SConstruction.SimplexHABeadWordBoundaryZero → IC.DGNerve.PullbackEquation |
| R64 | KST.SConstruction.SimplexHABeadWordCells |  禁止依存 299 本；KST.SConstruction.SimplexHABeadWordCells → KST.SConstruction.SerreCubeTopMappedComposition |
| R64 | KST.SConstruction.SimplexHABeadWordDecode |  禁止依存 91 本；KST.SConstruction.SimplexHABeadWordDecode → KST.SConstruction.SerreCubeGeneratorFaces |
| R64 | KST.SConstruction.SimplexHABeadWordRawValues |  禁止依存 304 本；KST.SConstruction.SimplexHABeadWordRawValues → KST.SConstruction.SimplexHABeadWordRecovery |
| R64 | KST.SConstruction.SimplexHABeadWordRecovery |  禁止依存 303 本；KST.SConstruction.SimplexHABeadWordRecovery → KST.SConstruction.CubicalLambdaNativeCellComponent |
| R64 | KST.SConstruction.SimplexHABeadWordTransport |  禁止依存 300 本；KST.SConstruction.SimplexHABeadWordTransport → KST.SConstruction.SimplexHABeadWordCells |
| R64 | KST.SConstruction.SimplexHABeadWordValues |  禁止依存 31 本；KST.SConstruction.SimplexHABeadWordValues → IC.DGNerve.FunctorMapping |
| R64 | KST.SConstruction.SimplexIntervalComposeOneFace |  禁止依存 222 本；KST.SConstruction.SimplexIntervalComposeOneFace → KST.SConstruction.ConcreteCubeFaceConjugation |
| R64 | KST.SConstruction.SimplexIntervalComposeRefinement |  禁止依存 205 本；KST.SConstruction.SimplexIntervalComposeRefinement → KST.SConstruction.NecklaceWedgeBeadOneFace |
| R64 | KST.SConstruction.SimplexIntervalComposeStandardCube |  禁止依存 461 本；KST.SConstruction.SimplexIntervalComposeStandardCube → KST.SConstruction.SimplexHAStrictIntervalSplit |
| R64 | KST.SConstruction.SimplexIntervalComposeStandardSerre |  禁止依存 462 本；KST.SConstruction.SimplexIntervalComposeStandardSerre → KST.SConstruction.SerreCubeRightExtensionFace |
| R64 | KST.SConstruction.SimplexIntervalComposition |  禁止依存 186 本；KST.SConstruction.SimplexIntervalComposition → KST.SConstruction.NecklaceCubicalComposition |
| R64 | KST.SConstruction.SimplexIntervalCompositionCoordinates |  禁止依存 187 本；KST.SConstruction.SimplexIntervalCompositionCoordinates → KST.SConstruction.SimplexIntervalComposition |
| R64 | KST.SConstruction.SimplexIntervalCompositionSeam |  禁止依存 188 本；KST.SConstruction.SimplexIntervalCompositionSeam → KST.SConstruction.SimplexIntervalCompositionCoordinates |
| R64 | KST.SConstruction.SimplexIntervalCubeCoordinates |  禁止依存 170 本；KST.SConstruction.SimplexIntervalCubeCoordinates → KST.SConstruction.SimplexIntervalCubicalOperators |
| R64 | KST.SConstruction.SimplexIntervalCubicalMapping |  禁止依存 166 本；KST.SConstruction.SimplexIntervalCubicalMapping → KST.SConstruction.NecklaceSimplexIntervalTerminal |
| R64 | KST.SConstruction.SimplexIntervalCubicalOperators |  禁止依存 169 本；KST.SConstruction.SimplexIntervalCubicalOperators → KST.SConstruction.NecklaceCubicalPostcomposition |
| R64 | KST.SConstruction.SimplexIntervalLambdaCell |  禁止依存 309 本；KST.SConstruction.SimplexIntervalLambdaCell → KST.SConstruction.NecklaceLambdaComposition |
| R64 | KST.SConstruction.SimplexIntervalLambdaGeneratorExt |  禁止依存 287 本；KST.SConstruction.SimplexIntervalLambdaGeneratorExt → KST.SConstruction.SerreCubeFaceTopExt |
| R64 | KST.SConstruction.SimplexIntervalLambdaHom |  禁止依存 272 本；KST.SConstruction.SimplexIntervalLambdaHom → KST.SConstruction.CubicalLambdaComonoids |
| R64 | KST.SConstruction.SimplexIntervalLambdaOperators |  禁止依存 277 本；KST.SConstruction.SimplexIntervalLambdaOperators → KST.SConstruction.SimplexIntervalLambdaHom |
| R64 | KST.SConstruction.SimplexIntervalLambdaStandardComposition |  禁止依存 476 本；KST.SConstruction.SimplexIntervalLambdaStandardComposition → KST.SConstruction.SerreCubeTensorCompositionTransport |
| R64 | KST.SConstruction.SimplexIntervalOperatorLaws |  禁止依存 263 本；KST.SConstruction.SimplexIntervalOperatorLaws → KST.SConstruction.SimplexIntervalCubicalOperators |
| R64 | KST.SConstruction.SimplexIntervalOperators |  禁止依存 166 本；KST.SConstruction.SimplexIntervalOperators → KST.SConstruction.NecklaceSimplexIntervalTerminal |
| R64 | KST.SConstruction.SimplexIntervalReverseHom |  禁止依存 256 本；KST.SConstruction.SimplexIntervalReverseHom → KST.SConstruction.CubicalLambda |
| R64 | KST.SConstruction.SimplexIntervalSerreComposition |  禁止依存 310 本；KST.SConstruction.SimplexIntervalSerreComposition → KST.SConstruction.SimplexIntervalLambdaCell |
| R64 | KST.SConstruction.SimplexSubsetCoordinateInclusion |  禁止依存 171 本；KST.SConstruction.SimplexSubsetCoordinateInclusion → KST.SConstruction.SimplexSubsetNonjointInclusion |
| R64 | KST.SConstruction.SimplexSubsetCoordinateSign |  禁止依存 189 本；KST.SConstruction.SimplexSubsetCoordinateSign → KST.SConstruction.NecklaceSingleCoordinateValue |
| R64 | KST.SConstruction.SimplexSubsetCubicalCell |  禁止依存 167 本；KST.SConstruction.SimplexSubsetCubicalCell → KST.SConstruction.NecklaceCubicalMapping |
| R64 | KST.SConstruction.SimplexSubsetCubicalInclusion |  禁止依存 170 本；KST.SConstruction.SimplexSubsetCubicalInclusion → KST.SConstruction.NecklaceSimplexSubsetAt |
| R64 | KST.SConstruction.SimplexSubsetEraseCoordinates |  禁止依存 175 本；KST.SConstruction.SimplexSubsetEraseCoordinates → KST.SConstruction.NecklaceSimplexSubsetErase |
| R64 | KST.SConstruction.SimplexSubsetEraseNormalizedFace |  禁止依存 185 本；KST.SConstruction.SimplexSubsetEraseNormalizedFace → KST.SConstruction.SimplexSubsetCubicalInclusion |
| R64 | KST.SConstruction.SimplexSubsetEraseZeroFace |  禁止依存 182 本；KST.SConstruction.SimplexSubsetEraseZeroFace → KST.SConstruction.ConcreteCubeZeroFaceCriterion |
| R64 | KST.SConstruction.SimplexSubsetImageFactorMap |  禁止依存 2 本；KST.SConstruction.SimplexSubsetImageFactorMap → KST.SConstruction.SimplexSubsetImageFactorOrder |
| R64 | KST.SConstruction.SimplexSubsetImageFactorOrder |  禁止依存 1 本；KST.SConstruction.SimplexSubsetImageFactorOrder → IC.DGNerve.Index |
| R64 | KST.SConstruction.SimplexSubsetImageSerreFactor |  禁止依存 295 本；KST.SConstruction.SimplexSubsetImageSerreFactor → KST.SConstruction.NecklaceLambdaCellPostcomposition |
| R64 | KST.SConstruction.SimplexSubsetInclusionCoordinates |  禁止依存 169 本；KST.SConstruction.SimplexSubsetInclusionCoordinates → KST.SConstruction.NecklaceSimplexSubsetInclusion |
| R64 | KST.SConstruction.SimplexSubsetInclusionRange |  禁止依存 171 本；KST.SConstruction.SimplexSubsetInclusionRange → KST.SConstruction.SimplexSubsetNonjointInclusion |
| R64 | KST.SConstruction.SimplexSubsetInteriorCoordinates |  禁止依存 198 本；KST.SConstruction.SimplexSubsetInteriorCoordinates → KST.SConstruction.SimplexSubsetCoordinateSign |
| R64 | KST.SConstruction.SimplexSubsetInteriorSum |  禁止依存 199 本；KST.SConstruction.SimplexSubsetInteriorSum → KST.SConstruction.SimplexSubsetInteriorCoordinates |
| R64 | KST.SConstruction.SimplexSubsetLambdaAugmentation |  禁止依存 294 本；KST.SConstruction.SimplexSubsetLambdaAugmentation → KST.SConstruction.SimplexDiagonalLambdaHom |
| R64 | KST.SConstruction.SimplexSubsetLambdaCell |  禁止依存 281 本；KST.SConstruction.SimplexSubsetLambdaCell → KST.SConstruction.CubicalLambdaComonoids |
| R64 | KST.SConstruction.SimplexSubsetLambdaCellAtDimension |  禁止依存 286 本；KST.SConstruction.SimplexSubsetLambdaCellAtDimension → KST.SConstruction.SimplexSubsetLambdaInclusion |
| R64 | KST.SConstruction.SimplexSubsetLambdaEraseFace |  禁止依存 296 本；KST.SConstruction.SimplexSubsetLambdaEraseFace → KST.SConstruction.SimplexSubsetEraseNormalizedFace |
| R64 | KST.SConstruction.SimplexSubsetLambdaGeneratorNecklace |  禁止依存 320 本；KST.SConstruction.SimplexSubsetLambdaGeneratorNecklace → KST.SConstruction.CubicalLambdaNativeSimplexData |
| R64 | KST.SConstruction.SimplexSubsetLambdaImageCell |  禁止依存 306 本；KST.SConstruction.SimplexSubsetLambdaImageCell → KST.SConstruction.NecklaceLambdaCellPostcomposition |
| R64 | KST.SConstruction.SimplexSubsetLambdaInclusion |  禁止依存 285 本；KST.SConstruction.SimplexSubsetLambdaInclusion → KST.SConstruction.SimplexSubsetCubicalInclusion |
| R64 | KST.SConstruction.SimplexSubsetLambdaNecklaceCell |  禁止依存 289 本；KST.SConstruction.SimplexSubsetLambdaNecklaceCell → KST.SConstruction.NecklaceLambdaCell |
| R64 | KST.SConstruction.SimplexSubsetLambdaNecklaceComparison |  禁止依存 309 本；KST.SConstruction.SimplexSubsetLambdaNecklaceComparison → KST.SConstruction.SerreCubeComplexDimensionComparison |
| R64 | KST.SConstruction.SimplexSubsetLambdaSpecifiedFace |  禁止依存 299 本；KST.SConstruction.SimplexSubsetLambdaSpecifiedFace → KST.SConstruction.SerreCubeChainFace |
| R64 | KST.SConstruction.SimplexSubsetLambdaSpecifiedOneDimension |  禁止依存 336 本；KST.SConstruction.SimplexSubsetLambdaSpecifiedOneDimension → KST.SConstruction.SerreCubeChainCompositionComparison |
| R64 | KST.SConstruction.SimplexSubsetLambdaSpecifiedOneFace |  禁止依存 331 本；KST.SConstruction.SimplexSubsetLambdaSpecifiedOneFace → KST.SConstruction.NecklaceLambdaComposition |
| R64 | KST.SConstruction.SimplexSubsetMappedFaceTop |  禁止依存 333 本；KST.SConstruction.SimplexSubsetMappedFaceTop → IC.DGNerve.LinearBoundary |
| R64 | KST.SConstruction.SimplexSubsetMappedOneFaceTop |  禁止依存 355 本；KST.SConstruction.SimplexSubsetMappedOneFaceTop → KST.SConstruction.SimplexSubsetMappedFaceTop |
| R64 | KST.SConstruction.SimplexSubsetNonjointInclusion |  禁止依存 170 本；KST.SConstruction.SimplexSubsetNonjointInclusion → KST.SConstruction.SimplexSubsetInclusionCoordinates |
| R64 | KST.SConstruction.SimplexSubsetSplitAugmentation |  禁止依存 192 本；KST.SConstruction.SimplexSubsetSplitAugmentation → KST.SConstruction.NecklaceSimplexSubsetAt |
| R64 | KST.SConstruction.SimplexSubsetSplitBlocks |  禁止依存 175 本；KST.SConstruction.SimplexSubsetSplitBlocks → KST.SConstruction.SimplexSubsetSplitCard |
| R64 | KST.SConstruction.SimplexSubsetSplitCard |  禁止依存 174 本；KST.SConstruction.SimplexSubsetSplitCard → KST.SConstruction.SimplexSubsetSplitRange |
| R64 | KST.SConstruction.SimplexSubsetSplitCubicalTensor |  禁止依存 212 本；KST.SConstruction.SimplexSubsetSplitCubicalTensor → KST.SConstruction.NecklaceCubicalComposition |
| R64 | KST.SConstruction.SimplexSubsetSplitDegrees |  禁止依存 193 本；KST.SConstruction.SimplexSubsetSplitDegrees → KST.SConstruction.SimplexSubsetSplitAugmentation |
| R64 | KST.SConstruction.SimplexSubsetSplitFaceSign |  禁止依存 197 本；KST.SConstruction.SimplexSubsetSplitFaceSign → KST.SConstruction.SimplexSubsetCoordinateSign |
| R64 | KST.SConstruction.SimplexSubsetSplitFlatNormalization |  禁止依存 322 本；KST.SConstruction.SimplexSubsetSplitFlatNormalization → KST.SConstruction.SimplexSubsetSplitNormalizedLambda |
| R64 | KST.SConstruction.SimplexSubsetSplitLambdaCell |  禁止依存 306 本；KST.SConstruction.SimplexSubsetSplitLambdaCell → KST.SConstruction.NecklaceLambdaCell |
| R64 | KST.SConstruction.SimplexSubsetSplitMap |  禁止依存 189 本；KST.SConstruction.SimplexSubsetSplitMap → KST.SConstruction.NecklaceWedgeBeadOneFace |
| R64 | KST.SConstruction.SimplexSubsetSplitMappedTop |  禁止依存 314 本；KST.SConstruction.SimplexSubsetSplitMappedTop → KST.SConstruction.NecklaceLambdaMappedTop |
| R64 | KST.SConstruction.SimplexSubsetSplitNativeComposition |  禁止依存 335 本；KST.SConstruction.SimplexSubsetSplitNativeComposition → IC.DGNerve.BoundaryDecomposition |
| R64 | KST.SConstruction.SimplexSubsetSplitNormalizedComparison |  禁止依存 209 本；KST.SConstruction.SimplexSubsetSplitNormalizedComparison → KST.SConstruction.SimplexSubsetCubicalCell |
| R64 | KST.SConstruction.SimplexSubsetSplitNormalizedCube |  禁止依存 208 本；KST.SConstruction.SimplexSubsetSplitNormalizedCube → KST.SConstruction.ConcreteCubeFaceConjugation |
| R64 | KST.SConstruction.SimplexSubsetSplitNormalizedDimensions |  禁止依存 201 本；KST.SConstruction.SimplexSubsetSplitNormalizedDimensions → KST.SConstruction.SimplexSubsetEraseNormalizedFace |
| R64 | KST.SConstruction.SimplexSubsetSplitNormalizedLambda |  禁止依存 321 本；KST.SConstruction.SimplexSubsetSplitNormalizedLambda → KST.SConstruction.SimplexSubsetSplitLambdaCell |
| R64 | KST.SConstruction.SimplexSubsetSplitOneFace |  禁止依存 194 本；KST.SConstruction.SimplexSubsetSplitOneFace → KST.SConstruction.SimplexSubsetSplitRefinementComparison |
| R64 | KST.SConstruction.SimplexSubsetSplitRange |  禁止依存 173 本；KST.SConstruction.SimplexSubsetSplitRange → IC.DGNerve.Index |
| R64 | KST.SConstruction.SimplexSubsetSplitRefinement |  禁止依存 190 本；KST.SConstruction.SimplexSubsetSplitRefinement → KST.SConstruction.SimplexSubsetSplitMap |
| R64 | KST.SConstruction.SimplexSubsetSplitRefinementComparison |  禁止依存 193 本；KST.SConstruction.SimplexSubsetSplitRefinementComparison → KST.SConstruction.SimplexSubsetSplitAugmentation |
| R64 | KST.SConstruction.SimplexSubsetSplitTopComposition |  禁止依存 313 本；KST.SConstruction.SimplexSubsetSplitTopComposition → KST.SConstruction.NecklaceLambdaTopComposition |
| R64 | KST.SConstruction.SimplexSubsetUniformFaceBoundary |  禁止依存 361 本；KST.SConstruction.SimplexSubsetUniformFaceBoundary → KST.SConstruction.CubicalLambdaNativeCoordinateBoundary |
| R64 | KST.SConstruction.SimplexSubsetVertexIndex |  禁止依存 167 本；KST.SConstruction.SimplexSubsetVertexIndex → KST.SConstruction.NecklaceSimplexSubset |
| R64 | KST.SConstruction.StrictSimplicialTransformationComponent |  禁止依存 74 本；KST.SConstruction.StrictSimplicialTransformationComponent → KST.Spectra.StrictEnrichedTransformationNerve |
| R64 | KST.SConstruction.SuspensionAdjointInterval |  禁止依存 191 本；KST.SConstruction.SuspensionAdjointInterval → KST.SConstruction.LoopIntervalExt |
| R64 | KST.SConstruction.SuspensionAssembly |  禁止依存 501 本；KST.SConstruction.SuspensionAssembly → KST.SConstruction.CombinedBoundaryAssembly |
| R64 | KST.SConstruction.SuspensionAssemblyAdjoint |  禁止依存 505 本；KST.SConstruction.SuspensionAssemblyAdjoint → KST.SConstruction.SuspensionAssemblyNaturality |
| R64 | KST.SConstruction.SuspensionAssemblyEvaluation |  禁止依存 503 本；KST.SConstruction.SuspensionAssemblyEvaluation → KST.SConstruction.RawCofiberTensorEvaluation |
| R64 | KST.SConstruction.SuspensionAssemblyNaturality |  禁止依存 504 本；KST.SConstruction.SuspensionAssemblyNaturality → KST.SConstruction.CofiberProjectionNaturality |
| R64 | KST.SConstruction.SuspensionFamilyEvaluation |  禁止依存 147 本；KST.SConstruction.SuspensionFamilyEvaluation → KST.SConstruction.PointedSuspensionEvaluation |
| R64 | KST.SConstruction.SuspensionLocalizedEquivalence |  禁止依存 122 本；KST.SConstruction.SuspensionLocalizedEquivalence → KST.SConstruction.PointedMappingLocalizedImage |
| R64 | KST.SConstruction.SuspensionLoopEnrichedComposition |  禁止依存 124 本；KST.SConstruction.SuspensionLoopEnrichedComposition → KST.SConstruction.PointedMappingCompositionFamilies |
| R64 | KST.SConstruction.SuspensionLoopEnrichedPostcomposition |  禁止依存 126 本；KST.SConstruction.SuspensionLoopEnrichedPostcomposition → KST.SConstruction.PointedLoopEnrichment |
| R64 | KST.SConstruction.SuspensionLoopMappingIso |  禁止依存 32 本；KST.SConstruction.SuspensionLoopMappingIso → KST.Spectra.SpectrumMorphisms |
| R64 | KST.Spectra.AcyclicFibrationLifting |  禁止依存 100 本；KST.Spectra.AcyclicFibrationLifting → KST.Spectra.FibrationIntervalLifting |
| R64 | KST.Spectra.AcyclicKanLifting |  禁止依存 94 本；KST.Spectra.AcyclicKanLifting → KST.Spectra.NormalizedBoundaryFilling |
| R64 | KST.Spectra.AnodyneCofiberSource |  禁止依存 111 本；KST.Spectra.AnodyneCofiberSource → KST.Spectra.AnodyneMappingLifts |
| R64 | KST.Spectra.AnodyneHomotopyEquivalence |  禁止依存 89 本；KST.Spectra.AnodyneHomotopyEquivalence → HA.Simplicial.KanRelativeLifting |
| R64 | KST.Spectra.AnodyneMappingLifts |  禁止依存 41 本；KST.Spectra.AnodyneMappingLifts → KST.Spectra.PointedIntervalAnodyne |
| R64 | KST.Spectra.AnodynePointMappingComparison |  禁止依存 92 本；KST.Spectra.AnodynePointMappingComparison → KST.Spectra.AnodyneMappingLifts |
| R64 | KST.Spectra.AnodyneRelativeComparison |  禁止依存 90 本；KST.Spectra.AnodyneRelativeComparison → KST.Spectra.AnodyneHomotopyEquivalence |
| R64 | KST.Spectra.BasedLoopCone |  禁止依存 970 本；KST.Spectra.BasedLoopCone → IC.HomotopyLimits.SpectrumHomFibrations |
| R64 | KST.Spectra.BasedLoopSquare |  禁止依存 1009 本；KST.Spectra.BasedLoopSquare → IC.Stable.SuspensionSquare |
| R64 | KST.Spectra.BasedPathLoopRestriction |  禁止依存 72 本；KST.Spectra.BasedPathLoopRestriction → KST.Spectra.FreeIntervalBoundary |
| R64 | KST.Spectra.BoundaryFilling |  禁止依存 43 本；KST.Spectra.BoundaryFilling → KST.Spectra.AnodyneMappingLifts |
| R64 | KST.Spectra.CircleClassMap |  禁止依存 125 本；KST.Spectra.CircleClassMap → KST.Spectra.CircleMappingComponents |
| R64 | KST.Spectra.CircleIntegerComponents |  禁止依存 128 本；KST.Spectra.CircleIntegerComponents → KST.Spectra.CircleClassMap |
| R64 | KST.Spectra.CircleMappingComponents |  禁止依存 124 本；KST.Spectra.CircleMappingComponents → KST.Spectra.CirclePower |
| R64 | KST.Spectra.CircleParameterTriangle |  禁止依存 129 本；KST.Spectra.CircleParameterTriangle → KST.Spectra.EndpointCircle |
| R64 | KST.Spectra.CirclePower |  禁止依存 115 本；KST.Spectra.CirclePower → KST.Spectra.PointedKanReplacement |
| R64 | KST.Spectra.CirclePowerPositiveHomotopy |  禁止依存 125 本；KST.Spectra.CirclePowerPositiveHomotopy → KST.Spectra.CircleMappingComponents |
| R64 | KST.Spectra.CirclePowerPositiveNaturality |  禁止依存 130 本；KST.Spectra.CirclePowerPositiveNaturality → KST.Spectra.CirclePowerPositiveHomotopy |
| R64 | KST.Spectra.CircleReversalHomotopy |  禁止依存 612 本；KST.Spectra.CircleReversalHomotopy → KST.Spectra.CircleClassMap |
| R64 | KST.Spectra.CircleSmashLoopSwap |  禁止依存 160 本；KST.Spectra.CircleSmashLoopSwap → KST.Spectra.PostLoopIntegerPower |
| R64 | KST.Spectra.CircleSmashMappingIso |  禁止依存 135 本；KST.Spectra.CircleSmashMappingIso → KST.Spectra.CircleSmashMappingPullback |
| R64 | KST.Spectra.CircleSmashMappingPullback |  禁止依存 133 本；KST.Spectra.CircleSmashMappingPullback → KST.Spectra.CircleSmashTriangles |
| R64 | KST.Spectra.CircleSmashSwap |  禁止依存 130 本；KST.Spectra.CircleSmashSwap → KST.Spectra.CircleSmashTriangles |
| R64 | KST.Spectra.CircleSmashTriangles |  禁止依存 129 本；KST.Spectra.CircleSmashTriangles → KST.Spectra.ReducedSquarePullback |
| R64 | KST.Spectra.CofiberMappingPullback |  禁止依存 39 本；KST.Spectra.CofiberMappingPullback → KST.Spectra.PointedCofiber |
| R27 | KST.Spectra.CofibrantOmegaSequence | R27 の汎用17本の外：Ωスペクトル・構造射付き列に固有。呼出元の上方移動も規則8(b)で保留。 禁止依存 100 本；KST.Spectra.CofibrantOmegaSequence → KST.Spectra.CofibrantKanSequence |
| R27 | KST.Spectra.CoherentNerve | R27 の汎用17本の外：Ωスペクトル・構造射付き列に固有。呼出元の上方移動も規則8(b)で保留。 禁止依存 83 本；KST.Spectra.CoherentNerve → IC.Coherent.Quasicategory |
| R64 | KST.Spectra.CoherentPathCompositionFaces |  禁止依存 72 本；KST.Spectra.CoherentPathCompositionFaces → KST.Spectra.CoherentPathParameters |
| R64 | KST.Spectra.CoherentPathParameterFaces |  禁止依存 72 本；KST.Spectra.CoherentPathParameterFaces → KST.Spectra.CoherentPathParameters |
| R64 | KST.Spectra.CoherentPathParameters |  禁止依存 71 本；KST.Spectra.CoherentPathParameters → KST.Spectra.CoherentFlaggedPaths |
| R64 | KST.Spectra.CoherentSimplexCompositionFaces |  禁止依存 78 本；KST.Spectra.CoherentSimplexCompositionFaces → KST.Spectra.CoherentPathCompositionFaces |
| R64 | KST.Spectra.CoherentSimplexTraceFaces |  禁止依存 76 本；KST.Spectra.CoherentSimplexTraceFaces → KST.Spectra.CoherentPathParameterFaces |
| R64 | KST.Spectra.CoherentSimplexTraces |  禁止依存 74 本；KST.Spectra.CoherentSimplexTraces → IC.F1.Coherent.HomComparison |
| R64 | KST.Spectra.CoherentTetrahedronInitialTrace |  禁止依存 84 本；KST.Spectra.CoherentTetrahedronInitialTrace → KST.Spectra.CoherentSimplexCompositionFaces |
| R64 | KST.Spectra.CoherentTriangleDegenerateTrace |  禁止依存 80 本；KST.Spectra.CoherentTriangleDegenerateTrace → IC.F1.Coherent.ArrowData |
| R64 | KST.Spectra.CoherentTrianglePathIso |  禁止依存 73 本；KST.Spectra.CoherentTrianglePathIso → KST.Spectra.CoherentTrianglePathMaximum |
| R64 | KST.Spectra.CoherentTrianglePathMaximum |  禁止依存 72 本；KST.Spectra.CoherentTrianglePathMaximum → KST.Spectra.CoherentPathParameters |
| R64 | KST.Spectra.CoherentTrianglePathMinimum |  禁止依存 361 本；KST.Spectra.CoherentTrianglePathMinimum → IC.HomotopyLimits.CoherentPathMinimum |
| R64 | KST.Spectra.CoherentTriangleTraceRecovery |  禁止依存 76 本；KST.Spectra.CoherentTriangleTraceRecovery → KST.Spectra.CoherentSimplexTraces |
| R64 | KST.Spectra.EndpointCircle |  禁止依存 40 本；KST.Spectra.EndpointCircle → KST.Spectra.IntervalBoundary |
| R64 | KST.Spectra.EnrichedOrderedCylinderBridge |  禁止依存 69 本；KST.Spectra.EnrichedOrderedCylinderBridge → KST.Spectra.EnrichedOrderedCylinderReindex |
| R64 | KST.Spectra.EnrichedOrderedCylinderEvaluation |  禁止依存 70 本；KST.Spectra.EnrichedOrderedCylinderEvaluation → KST.Spectra.EnrichedOrderedCylinderBridge |
| R64 | KST.Spectra.EnrichedOrderedCylinderNerve |  禁止依存 66 本；KST.Spectra.EnrichedOrderedCylinderNerve → IC.F1.Coherent.NervePostcomposition |
| R64 | KST.Spectra.EnrichedOrderedCylinderReindex |  禁止依存 67 本；KST.Spectra.EnrichedOrderedCylinderReindex → KST.Spectra.EnrichedOrderedCylinderNerve |
| R64 | KST.Spectra.EnrichedParameterCylinderEdge |  禁止依存 70 本；KST.Spectra.EnrichedParameterCylinderEdge → KST.Spectra.EnrichedOrderedCylinderBridge |
| R64 | KST.Spectra.EnrichedParameterCylinderEdgeOrdinary |  禁止依存 74 本；KST.Spectra.EnrichedParameterCylinderEdgeOrdinary → IC.F1.Coherent.ArrowData |
| R64 | KST.Spectra.EnrichedParameterCylinderFiber |  禁止依存 67 本；KST.Spectra.EnrichedParameterCylinderFiber → KST.Spectra.EnrichedParameterCylinderNervePair |
| R64 | KST.Spectra.EnrichedParameterCylinderNervePair |  禁止依存 66 本；KST.Spectra.EnrichedParameterCylinderNervePair → IC.F1.Coherent.NervePostcomposition |
| R64 | KST.Spectra.EnrichedParameterCylinderNerveRestriction |  禁止依存 67 本；KST.Spectra.EnrichedParameterCylinderNerveRestriction → KST.Spectra.EnrichedParameterCylinderNervePair |
| R64 | KST.Spectra.EnrichedParameterCylinderTriangle |  禁止依存 87 本；KST.Spectra.EnrichedParameterCylinderTriangle → IC.F1.Coherent.HomOrdinary |
| R64 | KST.Spectra.EnrichedTransformationTriangleOuter |  禁止依存 70 本；KST.Spectra.EnrichedTransformationTriangleOuter → KST.Spectra.EnrichedOrderedCylinderBridge |
| R64 | KST.Spectra.EnrichedTransformationTriangleStages |  禁止依存 67 本；KST.Spectra.EnrichedTransformationTriangleStages → KST.Spectra.EnrichedOrderedCylinderNerve |
| R64 | KST.Spectra.FiberKanSequence |  禁止依存 95 本；KST.Spectra.FiberKanSequence → KST.Spectra.KanSequence |
| R64 | KST.Spectra.FiberOmegaSpectrum |  禁止依存 105 本；KST.Spectra.FiberOmegaSpectrum → KST.Spectra.CofibrantOmegaSequence |
| R64 | KST.Spectra.FibrationAdjacentComparison |  禁止依存 120 本；KST.Spectra.FibrationAdjacentComparison → KST.Spectra.RelativePathBoundaryLift |
| R64 | KST.Spectra.FibrationAdjacentEndpoint |  禁止依存 121 本；KST.Spectra.FibrationAdjacentEndpoint → KST.Spectra.FibrationAdjacentComparison |
| R64 | KST.Spectra.FibrationAdjacentFiberEndpoint |  禁止依存 122 本；KST.Spectra.FibrationAdjacentFiberEndpoint → KST.Spectra.FibrationAdjacentEndpoint |
| R64 | KST.Spectra.FibrationCodifferenceTriangleLift |  禁止依存 119 本；KST.Spectra.FibrationCodifferenceTriangleLift → KST.Spectra.PointedMappingComponents |
| R64 | KST.Spectra.FibrationCompositionTriangleLift |  禁止依存 119 本；KST.Spectra.FibrationCompositionTriangleLift → KST.Spectra.PointedMappingComponents |
| R64 | KST.Spectra.FibrationDifferenceTriangleLift |  禁止依存 119 本；KST.Spectra.FibrationDifferenceTriangleLift → KST.Spectra.PointedMappingComponents |
| R64 | KST.Spectra.FibrationEdgeComposition |  禁止依存 121 本；KST.Spectra.FibrationEdgeComposition → KST.Spectra.FibrationCompositionTriangleLift |
| R64 | KST.Spectra.FibrationIntervalLifting |  禁止依存 95 本；KST.Spectra.FibrationIntervalLifting → KST.Spectra.AcyclicKanLifting |
| R64 | KST.Spectra.FilteredHomotopyComparison |  禁止依存 63 本；KST.Spectra.FilteredHomotopyComparison → KST.Spectra.FilteredPointedHomotopy |
| R64 | KST.Spectra.FilteredHomotopyGroups |  禁止依存 63 本；KST.Spectra.FilteredHomotopyGroups → KST.Spectra.FilteredPointedHomotopy |
| R64 | KST.Spectra.FilteredKanSequence |  禁止依存 111 本；KST.Spectra.FilteredKanSequence → KST.Spectra.CofibrantOmegaSequence |
| R64 | KST.Spectra.FilteredKanSequenceForgetful |  禁止依存 119 本；KST.Spectra.FilteredKanSequenceForgetful → KST.Spectra.FilteredKanSequence |
| R64 | KST.Spectra.FilteredKanSequenceMap |  禁止依存 130 本；KST.Spectra.FilteredKanSequenceMap → KST.Spectra.FilteredKanSequence |
| R64 | KST.Spectra.FunctionComplexComponents |  禁止依存 475 本；KST.Spectra.FunctionComplexComponents → KST.Spectra.FunctionComplexPost |
| R64 | KST.Spectra.FunctionComplexIsoFormula |  禁止依存 455 本；KST.Spectra.FunctionComplexIsoFormula → KST.Spectra.FreeActionEndNaturality |
| R64 | KST.Spectra.FunctionComplexPost |  禁止依存 474 本；KST.Spectra.FunctionComplexPost → KST.Spectra.GroupCochainHomotopyDiagram |
| R64 | KST.Spectra.HomotopyFiberVanishing |  禁止依存 127 本；KST.Spectra.HomotopyFiberVanishing → KST.Spectra.SpectrumHomotopyEquivalences |
| R64 | KST.Spectra.HomotopyTotalizationEvaluation |  禁止依存 690 本；KST.Spectra.HomotopyTotalizationEvaluation → KST.Spectra.OmegaSpectrumReplacedTotalization |
| R64 | KST.Spectra.HomotopyTotalizationMilnorComparison |  禁止依存 692 本；KST.Spectra.HomotopyTotalizationMilnorComparison → KST.Spectra.HomotopyTotalizationTower |
| R64 | KST.Spectra.HomotopyTotalizationMilnorExactness |  禁止依存 693 本；KST.Spectra.HomotopyTotalizationMilnorExactness → KST.Spectra.HomotopyTotalizationMilnorComparison |
| R64 | KST.Spectra.HomotopyTotalizationTower |  禁止依存 691 本；KST.Spectra.HomotopyTotalizationTower → KST.Spectra.HomotopyTotalizationEvaluation |
| R64 | KST.Spectra.HornMissingFaceComparison |  禁止依存 91 本；KST.Spectra.HornMissingFaceComparison → KST.Spectra.AnodyneRelativeComparison |
| R64 | KST.Spectra.InternalHomExchangeStrength |  禁止依存 27 本；KST.Spectra.InternalHomExchangeStrength → KST.Spectra.SuspensionLoop |
| R64 | KST.Spectra.IntervalBoundary |  禁止依存 39 本；KST.Spectra.IntervalBoundary → KST.Spectra.PointedInterval |
| R64 | KST.Spectra.IntervalContraction |  禁止依存 40 本；KST.Spectra.IntervalContraction → KST.Spectra.PointedInterval |
| R64 | KST.Spectra.KanAdjointNaturality |  禁止依存 194 本；KST.Spectra.KanAdjointNaturality → KST.Spectra.PointedComponentCancellation |
| R64 | KST.Spectra.KanCompositeCancellation |  禁止依存 410 本；KST.Spectra.KanCompositeCancellation → KST.Spectra.KanEquivalenceBridge |
| R64 | KST.Spectra.KanEquivalenceBridge |  禁止依存 409 本；KST.Spectra.KanEquivalenceBridge → IC.HomotopyLimits.BousfieldKanHomotopyInvariance |
| R64 | KST.Spectra.KanHomotopyEndSkeletalTower |  禁止依存 453 本；KST.Spectra.KanHomotopyEndSkeletalTower → KST.Spectra.KanSequenceHomotopyLimit |
| R64 | KST.Spectra.KanLoopCounitCoordinates |  禁止依存 599 本；KST.Spectra.KanLoopCounitCoordinates → KST.Spectra.SpectrumKanAdjointParameterNaturality |
| R64 | KST.Spectra.KanLoopExchangeSign |  禁止依存 170 本；KST.Spectra.KanLoopExchangeSign → KST.Spectra.DoubleCircleLoopExchange |
| R64 | KST.Spectra.KanLoopLift |  禁止依存 126 本；KST.Spectra.KanLoopLift → KST.Spectra.CircleMappingComponents |
| R27 | KST.Spectra.KanSequence | R27 の汎用17本の外：Ωスペクトル・構造射付き列に固有。呼出元の上方移動も規則8(b)で保留。 禁止依存 93 本；KST.Spectra.KanSequence → KST.Spectra.OmegaSpectrum |
| R64 | KST.Spectra.KanSequenceAdjointMap |  禁止依存 95 本；KST.Spectra.KanSequenceAdjointMap → KST.Spectra.KanSequenceCategory |
| R64 | KST.Spectra.KanSequenceCategory |  禁止依存 94 本；KST.Spectra.KanSequenceCategory → KST.Spectra.KanSequence |
| R64 | KST.Spectra.KanSequenceForgetful |  禁止依存 117 本；KST.Spectra.KanSequenceForgetful → KST.Spectra.FilteredOmegaSpectrum |
| R64 | KST.Spectra.KanSequenceHomotopyLimit |  禁止依存 443 本；KST.Spectra.KanSequenceHomotopyLimit → KST.Spectra.FilteredKanSequence |
| R64 | KST.Spectra.KanSequenceHomotopyLimitCone |  禁止依存 446 本；KST.Spectra.KanSequenceHomotopyLimitCone → KST.Spectra.KanSequenceHomotopyLimit |
| R64 | KST.Spectra.KanSequenceHomotopyLimitEnd |  禁止依存 454 本；KST.Spectra.KanSequenceHomotopyLimitEnd → KST.Spectra.KanSequenceHomotopyLimitUniversal |
| R64 | KST.Spectra.KanSequenceHomotopyLimitEvaluation |  禁止依存 449 本；KST.Spectra.KanSequenceHomotopyLimitEvaluation → KST.Spectra.KanSequenceHomotopyLimit |
| R64 | KST.Spectra.KanSequenceHomotopyLimitLevelLimit |  禁止依存 455 本；KST.Spectra.KanSequenceHomotopyLimitLevelLimit → KST.Spectra.KanSequenceHomotopyLimitEnd |
| R64 | KST.Spectra.KanSequenceHomotopyLimitMap |  禁止依存 447 本；KST.Spectra.KanSequenceHomotopyLimitMap → KST.Spectra.KanSequenceHomotopyLimit |
| R64 | KST.Spectra.KanSequenceHomotopyLimitUniversal |  禁止依存 453 本；KST.Spectra.KanSequenceHomotopyLimitUniversal → KST.Spectra.KanSequenceHomotopyLimitWedge |
| R64 | KST.Spectra.KanSequenceHomotopyLimitWedge |  禁止依存 452 本；KST.Spectra.KanSequenceHomotopyLimitWedge → KST.Spectra.KanSequenceHomotopyLimitEvaluation |
| R64 | KST.Spectra.KanSequenceLevelIso |  禁止依存 95 本；KST.Spectra.KanSequenceLevelIso → KST.Spectra.KanSequenceCategory |
| R64 | KST.Spectra.KanSequenceLevelIsoMap |  禁止依存 96 本；KST.Spectra.KanSequenceLevelIsoMap → KST.Spectra.KanSequenceLevelIso |
| R64 | KST.Spectra.KanSequenceLevelLimits |  禁止依存 95 本；KST.Spectra.KanSequenceLevelLimits → KST.Spectra.KanSequenceCategory |
| R64 | KST.Spectra.KanSequenceMappingExchange |  禁止依存 101 本；KST.Spectra.KanSequenceMappingExchange → KST.Spectra.KanSequenceMappingFunctor |
| R64 | KST.Spectra.KanSequenceMappingFunctor |  禁止依存 100 本；KST.Spectra.KanSequenceMappingFunctor → KST.Spectra.KanSequenceCategory |
| R64 | KST.Spectra.KanSequenceMappingParameter |  禁止依存 102 本；KST.Spectra.KanSequenceMappingParameter → KST.Spectra.KanSequenceMappingExchange |
| R64 | KST.Spectra.KanSequenceReplacement |  禁止依存 99 本；KST.Spectra.KanSequenceReplacement → KST.Spectra.KanSequence |
| R64 | KST.Spectra.KanSequenceWeightedDiagram |  禁止依存 420 本；KST.Spectra.KanSequenceWeightedDiagram → KST.Spectra.FreeIntervalBoundary |
| R64 | KST.Spectra.LoopBoundaryRepresentatives |  禁止依存 130 本；KST.Spectra.LoopBoundaryRepresentatives → KST.Spectra.LoopConnectingFiberEndpoint |
| R64 | KST.Spectra.LoopCircleBousfieldKanComparison |  禁止依存 198 本；KST.Spectra.LoopCircleBousfieldKanComparison → KST.Spectra.CospanBousfieldKanLoopComparison |
| R64 | KST.Spectra.LoopConeSquareVertex |  禁止依存 78 本；KST.Spectra.LoopConeSquareVertex → IC.Stable.SliceSquareDiagramEvaluation |
| R64 | KST.Spectra.LoopConnectingAnticommutation |  禁止依存 132 本；KST.Spectra.LoopConnectingAnticommutation → KST.Spectra.LoopConnectingStandardRepresentatives |
| R64 | KST.Spectra.LoopConnectingFiberEndpoint |  禁止依存 129 本；KST.Spectra.LoopConnectingFiberEndpoint → KST.Spectra.LoopConnectingPathOutput |
| R64 | KST.Spectra.LoopConnectingPathLift |  禁止依存 126 本；KST.Spectra.LoopConnectingPathLift → KST.Spectra.FibrationAdjacentFiberEndpoint |
| R64 | KST.Spectra.LoopConnectingPathOutput |  禁止依存 128 本；KST.Spectra.LoopConnectingPathOutput → KST.Spectra.LoopConnectingPathLift |
| R64 | KST.Spectra.LoopConnectingStandardRepresentatives |  禁止依存 131 本；KST.Spectra.LoopConnectingStandardRepresentatives → KST.Spectra.LoopBoundaryRepresentatives |
| R64 | KST.Spectra.LoopConnectingZeroAnticommutation |  禁止依存 134 本；KST.Spectra.LoopConnectingZeroAnticommutation → KST.Spectra.LoopConnectingStandardRepresentatives |
| R64 | KST.Spectra.LoopConnectingZeroFiber |  禁止依存 130 本；KST.Spectra.LoopConnectingZeroFiber → KST.Spectra.LoopConnectingFiberEndpoint |
| R64 | KST.Spectra.LoopEdgewiseSectionFaces |  禁止依存 437 本；KST.Spectra.LoopEdgewiseSectionFaces → KST.Spectra.CospanPrefixCoordinates |
| R64 | KST.Spectra.LoopExchangeFamily |  禁止依存 615 本；KST.Spectra.LoopExchangeFamily → KST.Spectra.PointedBasedPathCalculus |
| R64 | KST.Spectra.LoopExchangeFamilyCoordinates |  禁止依存 670 本；KST.Spectra.LoopExchangeFamilyCoordinates → KST.Spectra.DeloopedExchangeSquareCoordinates |
| R64 | KST.Spectra.LoopExchangeFamilyNaturality |  禁止依存 688 本；KST.Spectra.LoopExchangeFamilyNaturality → KST.Spectra.LoopExchangeFamilyNaturalityImage |
| R64 | KST.Spectra.LoopExchangeFamilyNaturalityImage |  禁止依存 682 本；KST.Spectra.LoopExchangeFamilyNaturalityImage → KST.Spectra.ConstantBoundarySquareCodifference |
| R64 | KST.Spectra.LoopExchangeFamilyNaturalitySides |  禁止依存 677 本；KST.Spectra.LoopExchangeFamilyNaturalitySides → KST.Spectra.LoopExchangeFamilyCoordinates |
| R64 | KST.Spectra.LoopExchangeFamilyPostPasting |  禁止依存 673 本；KST.Spectra.LoopExchangeFamilyPostPasting → KST.Spectra.ConstantBoundarySquarePasting |
| R64 | KST.Spectra.LoopExchangeFamilyPostSquares |  禁止依存 669 本；KST.Spectra.LoopExchangeFamilyPostSquares → KST.Spectra.LoopExchangeFamilyTrace |
| R64 | KST.Spectra.LoopExchangeFamilyPreSquare |  禁止依存 669 本；KST.Spectra.LoopExchangeFamilyPreSquare → KST.Spectra.LoopExchangeFamilyTrace |
| R64 | KST.Spectra.LoopExchangeFamilyTrace |  禁止依存 668 本；KST.Spectra.LoopExchangeFamilyTrace → KST.Spectra.DeloopedTracedExchange |
| R64 | KST.Spectra.LoopExchangeOperators |  禁止依存 126 本；KST.Spectra.LoopExchangeOperators → KST.Spectra.CircleClassMap |
| R64 | KST.Spectra.LoopFiber |  禁止依存 63 本；KST.Spectra.LoopFiber → KST.Spectra.PointedFiber |
| R64 | KST.Spectra.LoopFundamentalCommutativity |  禁止依存 66 本；KST.Spectra.LoopFundamentalCommutativity → KST.Spectra.PositiveLoopNaturality |
| R64 | KST.Spectra.LoopHomotopyGroups |  禁止依存 51 本；KST.Spectra.LoopHomotopyGroups → KST.Spectra.LoopPathFiber |
| R64 | KST.Spectra.LoopHomotopyNaturality |  禁止依存 63 本；KST.Spectra.LoopHomotopyNaturality → KST.Spectra.LoopZeroHomotopy |
| R64 | KST.Spectra.LoopIntegerPower |  禁止依存 135 本；KST.Spectra.LoopIntegerPower → KST.Spectra.LoopInversion |
| R64 | KST.Spectra.LoopIntervalEndCircleIso |  禁止依存 72 本；KST.Spectra.LoopIntervalEndCircleIso → KST.Spectra.CofiberMappingFamilies |
| R64 | KST.Spectra.LoopIntervalEndFamilies |  禁止依存 64 本；KST.Spectra.LoopIntervalEndFamilies → IC.HomotopyLimits.WeightedSections |
| R64 | KST.Spectra.LoopInversion |  禁止依存 132 本；KST.Spectra.LoopInversion → KST.Spectra.CircleIntegerComponents |
| R64 | KST.Spectra.LoopMapBasedDetection |  禁止依存 94 本；KST.Spectra.LoopMapBasedDetection → KST.Spectra.LoopHomotopyNaturality |
| R64 | KST.Spectra.LoopMappingClasses |  禁止依存 125 本；KST.Spectra.LoopMappingClasses → KST.Spectra.CircleMappingComponents |
| R64 | KST.Spectra.LoopMappingOperations |  禁止依存 126 本；KST.Spectra.LoopMappingOperations → KST.Spectra.LoopMappingClasses |
| R64 | KST.Spectra.LoopMappingPositiveEquiv |  禁止依存 137 本；KST.Spectra.LoopMappingPositiveEquiv → KST.Spectra.PositiveLoopNaturality |
| R64 | KST.Spectra.LoopMappingTargetNaturality |  禁止依存 137 本；KST.Spectra.LoopMappingTargetNaturality → KST.Spectra.LoopMappingClasses |
| R64 | KST.Spectra.LoopMappingZeroOrientation |  禁止依存 182 本；KST.Spectra.LoopMappingZeroOrientation → KST.Spectra.LoopMappingClasses |
| R64 | KST.Spectra.LoopMultiplication |  禁止依存 127 本；KST.Spectra.LoopMultiplication → KST.Spectra.LoopMappingOperations |
| R64 | KST.Spectra.LoopParameterIntegerPower |  禁止依存 136 本；KST.Spectra.LoopParameterIntegerPower → KST.Spectra.LoopIntegerPower |
| R64 | KST.Spectra.LoopPathFiber |  禁止依存 50 本；KST.Spectra.LoopPathFiber → KST.Spectra.CofiberMappingPullback |
| R64 | KST.Spectra.LoopPathVertices |  禁止依存 122 本；KST.Spectra.LoopPathVertices → KST.Spectra.MappingFiberPaths |
| R64 | KST.Spectra.LoopPositivePower |  禁止依存 129 本；KST.Spectra.LoopPositivePower → KST.Spectra.LoopMultiplication |
| R64 | KST.Spectra.LoopSignComponents |  禁止依存 140 本；KST.Spectra.LoopSignComponents → KST.Spectra.LoopMappingTargetNaturality |
| R64 | KST.Spectra.LoopTraceContraction |  禁止依存 117 本；KST.Spectra.LoopTraceContraction → KST.Spectra.FundamentalLoopHomotopyCategory |
| R64 | KST.Spectra.LoopZeroHomotopy |  禁止依存 56 本；KST.Spectra.LoopZeroHomotopy → KST.Spectra.LoopHomotopyGroups |
| R64 | KST.Spectra.LoopZeroOrientation |  禁止依存 166 本；KST.Spectra.LoopZeroOrientation → KST.Spectra.LoopBoundaryRepresentatives |
| R64 | KST.Spectra.LoopZeroPenultimate |  禁止依存 67 本；KST.Spectra.LoopZeroPenultimate → KST.Spectra.LoopZeroHomotopy |
| R64 | KST.Spectra.MappingPathSequence |  禁止依存 109 本；KST.Spectra.MappingPathSequence → KST.Spectra.CofibrantOmegaSequence |
| R64 | KST.Spectra.MappingPathSpace |  禁止依存 100 本；KST.Spectra.MappingPathSpace → KST.Spectra.FreeIntervalBoundary |
| R64 | KST.Spectra.MonoRightHomotopyEquivalence |  禁止依存 91 本；KST.Spectra.MonoRightHomotopyEquivalence → HA.Simplicial.MonoRightLiftingRelativeHomotopy |
| R64 | KST.Spectra.NullHomotopyDifferenceChange |  禁止依存 95 本；KST.Spectra.NullHomotopyDifferenceChange → KST.Spectra.NullHomotopyDifferenceComposition |
| R64 | KST.Spectra.NullHomotopyDifferenceClass |  禁止依存 92 本；KST.Spectra.NullHomotopyDifferenceClass → KST.Spectra.HornMissingFaceComparison |
| R64 | KST.Spectra.NullHomotopyDifferenceComposition |  禁止依存 93 本；KST.Spectra.NullHomotopyDifferenceComposition → KST.Spectra.NullHomotopyDifferenceClass |
| R64 | KST.Spectra.NullHomotopyDifferenceIdentity |  禁止依存 93 本；KST.Spectra.NullHomotopyDifferenceIdentity → KST.Spectra.NullHomotopyDifferenceClass |
| R64 | KST.Spectra.NullHomotopyDifferenceNaturality |  禁止依存 93 本；KST.Spectra.NullHomotopyDifferenceNaturality → KST.Spectra.NullHomotopyDifferenceClass |
| R64 | KST.Spectra.NullHomotopyEndpointLifting |  禁止依存 98 本；KST.Spectra.NullHomotopyEndpointLifting → KST.Spectra.NullHomotopyStrictLifting |
| R64 | KST.Spectra.NullHomotopyStrictLifting |  禁止依存 97 本；KST.Spectra.NullHomotopyStrictLifting → KST.Spectra.NullDifferenceZeroFiller |
| R64 | KST.Spectra.NullHomotopyTriangleAdjustment |  禁止依存 98 本；KST.Spectra.NullHomotopyTriangleAdjustment → KST.Spectra.NullDifferenceZeroFiller |
| R64 | KST.Spectra.NullHomotopyTriangleHorn |  禁止依存 95 本；KST.Spectra.NullHomotopyTriangleHorn → KST.Spectra.NullTransportDifference |
| R64 | KST.Spectra.NullHomotopyTriangleLifting |  禁止依存 102 本；KST.Spectra.NullHomotopyTriangleLifting → KST.Spectra.NullHomotopyEndpointLifting |
| R64 | KST.Spectra.OmegaSpectrum |  禁止依存 28 本；KST.Spectra.OmegaSpectrum → KST.Spectra.SuspensionLoop |
| R64 | KST.Spectra.OmegaSpectrumTransitions |  禁止依存 52 本；KST.Spectra.OmegaSpectrumTransitions → KST.Spectra.LoopHomotopyGroups |
| R64 | KST.Spectra.OmegaSpectrumZeroGroups |  禁止依存 58 本；KST.Spectra.OmegaSpectrumZeroGroups → KST.Spectra.LoopZeroHomotopy |
| R64 | KST.Spectra.PathContractibility |  禁止依存 45 本；KST.Spectra.PathContractibility → KST.Spectra.PathContraction |
| R64 | KST.Spectra.PathContraction |  禁止依存 44 本；KST.Spectra.PathContraction → KST.Spectra.PathContractionBody |
| R64 | KST.Spectra.PathContractionBody |  禁止依存 43 本；KST.Spectra.PathContractionBody → KST.Spectra.PathReparametrization |
| R64 | KST.Spectra.PathContractionEndpoint |  禁止依存 123 本；KST.Spectra.PathContractionEndpoint → KST.Comparison.BasedPathEndpoint |
| R64 | KST.Spectra.PathNaturality |  禁止依存 62 本；KST.Spectra.PathNaturality → KST.Spectra.LoopPathFiber |
| R64 | KST.Spectra.PathReparametrization |  禁止依存 41 本；KST.Spectra.PathReparametrization → KST.Spectra.IntervalContraction |
| R64 | KST.Spectra.PathSpace |  禁止依存 39 本；KST.Spectra.PathSpace → KST.Spectra.PointedInterval |
| R64 | KST.Spectra.PathTriangleBoundary |  禁止依存 53 本；KST.Spectra.PathTriangleBoundary → KST.Spectra.SphericalPathBoundary |
| R64 | KST.Spectra.PathVertexContraction |  禁止依存 124 本；KST.Spectra.PathVertexContraction → KST.Spectra.PathContractionEndpoint |
| R64 | KST.Spectra.PointedActionCochainBasepoint |  禁止依存 463 本；KST.Spectra.PointedActionCochainBasepoint → KST.Spectra.FunctionComplexIsoFormula |
| R64 | KST.Spectra.PointedActionCochainCotensor |  禁止依存 464 本；KST.Spectra.PointedActionCochainCotensor → KST.Spectra.PointedActionCochainEquivalence |
| R64 | KST.Spectra.PointedActionCochainEquivalence |  禁止依存 460 本；KST.Spectra.PointedActionCochainEquivalence → KST.Spectra.PointedActionCochains |
| R64 | KST.Spectra.PointedActionCochainHomotopy |  禁止依存 460 本；KST.Spectra.PointedActionCochainHomotopy → KST.Spectra.PointedActionCochains |
| R64 | KST.Spectra.PointedActionCochains |  禁止依存 459 本；KST.Spectra.PointedActionCochains → KST.Spectra.FreeCochainWeight |
| R64 | KST.Spectra.PointedActionDiagrams |  禁止依存 458 本；KST.Spectra.PointedActionDiagrams → KST.Spectra.PointedFreeActionEquivalence |
| R64 | KST.Spectra.PointedActionHomotopy |  禁止依存 63 本；KST.Spectra.PointedActionHomotopy → KST.Spectra.PointedHomotopyGroupDiagram |
| R64 | KST.Spectra.PointedBasedIntervalTraces |  禁止依存 607 本；KST.Spectra.PointedBasedIntervalTraces → KST.Spectra.PointedBasedPathClosed |
| R64 | KST.Spectra.PointedBasedPathCalculus |  禁止依存 604 本；KST.Spectra.PointedBasedPathCalculus → KST.Spectra.PointedVerticalChains |
| R64 | KST.Spectra.PointedBasedPathClosed |  禁止依存 606 本；KST.Spectra.PointedBasedPathClosed → KST.Spectra.PointedBasedPathCalculus |
| R64 | KST.Spectra.PointedBasedPathCodifference |  禁止依存 616 本；KST.Spectra.PointedBasedPathCodifference → KST.Spectra.FibrationCodifferenceTriangleLift |
| R64 | KST.Spectra.PointedBasedPathComposition |  禁止依存 614 本；KST.Spectra.PointedBasedPathComposition → KST.Spectra.PointedBasedIntervalTraces |
| R64 | KST.Spectra.PointedBasedPathDifference |  禁止依存 616 本；KST.Spectra.PointedBasedPathDifference → KST.Spectra.FibrationDifferenceTriangleLift |
| R64 | KST.Spectra.PointedBasedPathUncurry |  禁止依存 617 本；KST.Spectra.PointedBasedPathUncurry → KST.Spectra.PointedBasedPathDifference |
| R64 | KST.Spectra.PointedCochainDensity |  禁止依存 557 本；KST.Spectra.PointedCochainDensity → KST.Spectra.CochainDensityCone |
| R64 | KST.Spectra.PointedCochainDensityFunctor |  禁止依存 569 本；KST.Spectra.PointedCochainDensityFunctor → KST.Spectra.GroupUniversalCoverEnd |
| R64 | KST.Spectra.PointedCochainDensityNaturality |  禁止依存 565 本；KST.Spectra.PointedCochainDensityNaturality → KST.Spectra.CochainDensityCoefficient |
| R64 | KST.Spectra.PointedCofiber |  禁止依存 38 本；KST.Spectra.PointedCofiber → KST.Spectra.PointedEnrichment |
| R64 | KST.Spectra.PointedCofiberComparison |  禁止依存 65 本；KST.Spectra.PointedCofiberComparison → KST.Spectra.PointedCofiberUniversal |
| R64 | KST.Spectra.PointedCofiberCoproduct |  禁止依存 40 本；KST.Spectra.PointedCofiberCoproduct → KST.Spectra.PointedCofiberUniversal |
| R64 | KST.Spectra.PointedCofiberMappingFiberIso |  禁止依存 64 本；KST.Spectra.PointedCofiberMappingFiberIso → KST.Spectra.CofiberMappingFiberIso |
| R64 | KST.Spectra.PointedCofiberMappingNaturality |  禁止依存 66 本；KST.Spectra.PointedCofiberMappingNaturality → KST.Spectra.PointedCofiberMappingFiberIso |
| R64 | KST.Spectra.PointedCofiberPushout |  禁止依存 39 本；KST.Spectra.PointedCofiberPushout → KST.Spectra.PointedCofiber |
| R64 | KST.Spectra.PointedCofiberUniversal |  禁止依存 39 本；KST.Spectra.PointedCofiberUniversal → KST.Spectra.PointedCofiber |
| R64 | KST.Spectra.PointedComponentCancellation |  禁止依存 121 本；KST.Spectra.PointedComponentCancellation → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.Spectra.PointedComponentIsomorphism |  禁止依存 126 本；KST.Spectra.PointedComponentIsomorphism → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.Spectra.PointedConnectingRepresentatives |  禁止依存 115 本；KST.Spectra.PointedConnectingRepresentatives → KST.Spectra.PointedFibrationBoundary |
| R64 | KST.Spectra.PointedConstantIntervalSquare |  禁止依存 626 本；KST.Spectra.PointedConstantIntervalSquare → KST.Spectra.PointedIntervalNaturality |
| R64 | KST.Spectra.PointedCoproductHom |  禁止依存 473 本；KST.Spectra.PointedCoproductHom → KST.Spectra.CofiberMappingPullback |
| R64 | KST.Spectra.PointedCoproductHomNaturality |  禁止依存 480 本；KST.Spectra.PointedCoproductHomNaturality → KST.Spectra.FunctionComplexPost |
| R64 | KST.Spectra.PointedCosimplicialKanFunctor |  禁止依存 154 本；KST.Spectra.PointedCosimplicialKanFunctor → KST.Spectra.PointedCosimplicialKanReplacement |
| R64 | KST.Spectra.PointedCosimplicialKanReplacement |  禁止依存 153 本；KST.Spectra.PointedCosimplicialKanReplacement → KST.Spectra.CosimplicialKanReplacement |
| R64 | KST.Spectra.PointedCotensorCoordinateFamilies |  禁止依存 129 本；KST.Spectra.PointedCotensorCoordinateFamilies → KST.Spectra.ExponentialHomotopyEdges |
| R64 | KST.Spectra.PointedCotensorCoordinateHomotopies |  禁止依存 618 本；KST.Spectra.PointedCotensorCoordinateHomotopies → KST.Spectra.PointedBasedIntervalTraces |
| R64 | KST.Spectra.PointedCotensorCoordinates |  禁止依存 31 本；KST.Spectra.PointedCotensorCoordinates → KST.Spectra.FreePointedHomRestriction |
| R64 | KST.Spectra.PointedCotensorFamilyDescription |  禁止依存 133 本；KST.Spectra.PointedCotensorFamilyDescription → KST.Spectra.PointedCotensorCoordinateFamilies |
| R64 | KST.Spectra.PointedCotensorFamilyNaturality |  禁止依存 130 本；KST.Spectra.PointedCotensorFamilyNaturality → KST.Spectra.PointedCotensorCoordinateFamilies |
| R64 | KST.Spectra.PointedCotensorFamilyStructure |  禁止依存 616 本；KST.Spectra.PointedCotensorFamilyStructure → KST.Spectra.PointedCotensorFamilyNaturality |
| R64 | KST.Spectra.PointedCotensorIntervalEndpoints |  禁止依存 629 本；KST.Spectra.PointedCotensorIntervalEndpoints → KST.Spectra.FreeIntervalBoundary |
| R64 | KST.Spectra.PointedCotensorRelativeHomotopies |  禁止依存 619 本；KST.Spectra.PointedCotensorRelativeHomotopies → KST.Spectra.PointedCotensorCoordinateHomotopies |
| R64 | KST.Spectra.PointedCotensorStructureCoordinates |  禁止依存 554 本；KST.Spectra.PointedCotensorStructureCoordinates → KST.Spectra.PointedCotensorCoordinates |
| R64 | KST.Spectra.PointedCurryFamilyVertex |  禁止依存 121 本；KST.Spectra.PointedCurryFamilyVertex → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.Spectra.PointedCurryingComponents |  禁止依存 121 本；KST.Spectra.PointedCurryingComponents → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.Spectra.PointedCurryingParameterComponents |  禁止依存 121 本；KST.Spectra.PointedCurryingParameterComponents → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.Spectra.PointedEndpointLoopPullback |  禁止依存 73 本；KST.Spectra.PointedEndpointLoopPullback → KST.Spectra.BasedPathLoopRestriction |
| R64 | KST.Spectra.PointedEnrichment |  禁止依存 37 本；KST.Spectra.PointedEnrichment → CategoryTheory.Monoidal.TransportOrdinaryEnrichment |
| R64 | KST.Spectra.PointedEvaluationAction |  禁止依存 611 本；KST.Spectra.PointedEvaluationAction → KST.Spectra.PointedHomTransposeComponents |
| R64 | KST.Spectra.PointedExchangeVertices |  禁止依存 139 本；KST.Spectra.PointedExchangeVertices → KST.Spectra.LoopMappingPositiveEquiv |
| R64 | KST.Spectra.PointedExtension |  禁止依存 30 本；KST.Spectra.PointedExtension → HA.Simplicial.KanHomotopyExtension |
| R64 | KST.Spectra.PointedFactorization |  禁止依存 92 本；KST.Spectra.PointedFactorization → HA.Simplicial.Generators |
| R64 | KST.Spectra.PointedFiber |  禁止依存 62 本；KST.Spectra.PointedFiber → KST.Spectra.PointedHomotopy |
| R64 | KST.Spectra.PointedFiberComparison |  禁止依存 63 本；KST.Spectra.PointedFiberComparison → KST.Spectra.PointedFiber |
| R64 | KST.Spectra.PointedFibrationBoundary |  禁止依存 114 本；KST.Spectra.PointedFibrationBoundary → KST.Spectra.PointedFiber |
| R64 | KST.Spectra.PointedFibrationExactness |  禁止依存 115 本；KST.Spectra.PointedFibrationExactness → KST.Spectra.PointedFibrationBoundary |
| R64 | KST.Spectra.PointedFibrationNaturality |  禁止依存 116 本；KST.Spectra.PointedFibrationNaturality → KST.Spectra.PointedFiberComparison |
| R64 | KST.Spectra.PointedFreeActionEquivalence |  禁止依存 457 本；KST.Spectra.PointedFreeActionEquivalence → KST.Spectra.FreeActionEndEquivalence |
| R64 | KST.Spectra.PointedFreeIntervalBoundaryMap |  禁止依存 631 本；KST.Spectra.PointedFreeIntervalBoundaryMap → KST.Spectra.PointedCotensorIntervalEndpoints |
| R64 | KST.Spectra.PointedGroupFunctionCochains |  禁止依存 470 本；KST.Spectra.PointedGroupFunctionCochains → KST.Spectra.FreePointedFunctionNaturality |
| R64 | KST.Spectra.PointedGroupProduct |  禁止依存 62 本；KST.Spectra.PointedGroupProduct → KST.Spectra.PointedHomotopy |
| R64 | KST.Spectra.PointedHomDifferenceNaturality |  禁止依存 5 本；KST.Spectra.PointedHomDifferenceNaturality → KST.Spectra.FundamentalLoopNaturality |
| R64 | KST.Spectra.PointedHomTransposeComponents |  禁止依存 121 本；KST.Spectra.PointedHomTransposeComponents → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.Spectra.PointedHomotopy |  禁止依存 61 本；KST.Spectra.PointedHomotopy → KST.Spectra.PathContractibility |
| R64 | KST.Spectra.PointedHomotopyClasses |  禁止依存 120 本；KST.Spectra.PointedHomotopyClasses → KST.Spectra.PointedMappingComponents |
| R64 | KST.Spectra.PointedHomotopyExtension |  禁止依存 119 本；KST.Spectra.PointedHomotopyExtension → HA.Simplicial.KanFibrationEndpointExtension |
| R64 | KST.Spectra.PointedHomotopyGroupDiagram |  禁止依存 62 本；KST.Spectra.PointedHomotopyGroupDiagram → KST.Spectra.PointedHomotopy |
| R64 | KST.Spectra.PointedHomotopyLimit |  禁止依存 133 本；KST.Spectra.PointedHomotopyLimit → IC.HomotopyLimits.SectionsKan |
| R64 | KST.Spectra.PointedHomotopyLimitInvariance |  禁止依存 411 本；KST.Spectra.PointedHomotopyLimitInvariance → KST.Spectra.KanEquivalenceBridge |
| R64 | KST.Spectra.PointedIhomActionComposition |  禁止依存 608 本；KST.Spectra.PointedIhomActionComposition → KST.Spectra.PointedIhomIntervalAction |
| R64 | KST.Spectra.PointedIhomActionLaws |  禁止依存 609 本；KST.Spectra.PointedIhomActionLaws → KST.Spectra.PointedIhomActionComposition |
| R64 | KST.Spectra.PointedIhomActionNaturality |  禁止依存 608 本；KST.Spectra.PointedIhomActionNaturality → KST.Spectra.PointedIhomIntervalAction |
| R64 | KST.Spectra.PointedIhomActionSuspension |  禁止依存 609 本；KST.Spectra.PointedIhomActionSuspension → KST.Spectra.PointedIhomActionComposition |
| R64 | KST.Spectra.PointedIhomIntervalAction |  禁止依存 607 本；KST.Spectra.PointedIhomIntervalAction → KST.Spectra.PointedBasedPathClosed |
| R64 | KST.Spectra.PointedIhomIntervalNaturality |  禁止依存 611 本；KST.Spectra.PointedIhomIntervalNaturality → KST.Spectra.PointedIhomActionNaturality |
| R64 | KST.Spectra.PointedIhomParameterExchange |  禁止依存 614 本；KST.Spectra.PointedIhomParameterExchange → KST.Spectra.PointedEvaluationAction |
| R64 | KST.Spectra.PointedIhomParameterRestriction |  禁止依存 609 本；KST.Spectra.PointedIhomParameterRestriction → KST.Spectra.PointedIhomActionNaturality |
| R64 | KST.Spectra.PointedIhomStepInterval |  禁止依存 616 本；KST.Spectra.PointedIhomStepInterval → KST.Spectra.PointedIhomActionSuspension |
| R64 | KST.Spectra.PointedInterval |  禁止依存 38 本；KST.Spectra.PointedInterval → KST.Spectra.PointedEnrichment |
| R64 | KST.Spectra.PointedIntervalAnodyne |  禁止依存 39 本；KST.Spectra.PointedIntervalAnodyne → KST.Spectra.PointedInterval |
| R64 | KST.Spectra.PointedIntervalConjugateSquare |  禁止依存 614 本；KST.Spectra.PointedIntervalConjugateSquare → KST.Spectra.PointedIntervalCoordinateNaturality |
| R64 | KST.Spectra.PointedIntervalCoordinateNaturality |  禁止依存 605 本；KST.Spectra.PointedIntervalCoordinateNaturality → KST.Spectra.PointedBasedPathCalculus |
| R64 | KST.Spectra.PointedIntervalCotensorConjugation |  禁止依存 622 本；KST.Spectra.PointedIntervalCotensorConjugation → KST.Spectra.PointedIhomIntervalNaturality |
| R64 | KST.Spectra.PointedIntervalIhomSquare |  禁止依存 637 本；KST.Spectra.PointedIntervalIhomSquare → KST.Spectra.PointedIhomIntervalNaturality |
| R64 | KST.Spectra.PointedIntervalInputBoundary |  禁止依存 631 本；KST.Spectra.PointedIntervalInputBoundary → KST.Spectra.PointedIntervalInputSquare |
| R64 | KST.Spectra.PointedIntervalInputSquare |  禁止依存 625 本；KST.Spectra.PointedIntervalInputSquare → KST.Spectra.PointedPrecompositionSourceNaturality |
| R64 | KST.Spectra.PointedIntervalNaturality |  禁止依存 617 本；KST.Spectra.PointedIntervalNaturality → KST.Spectra.PointedBasedPathDifference |
| R64 | KST.Spectra.PointedIntervalProjectedNaturality |  禁止依存 707 本；KST.Spectra.PointedIntervalProjectedNaturality → KST.Spectra.CancellationFirstNaturality |
| R64 | KST.Spectra.PointedIntervalProjectedSquare |  禁止依存 708 本；KST.Spectra.PointedIntervalProjectedSquare → KST.Spectra.PointedIntervalProjectedNaturality |
| R64 | KST.Spectra.PointedIntervalProjectionNaturality |  禁止依存 615 本；KST.Spectra.PointedIntervalProjectionNaturality → KST.Spectra.PointedBasedPathComposition |
| R64 | KST.Spectra.PointedIntervalStrictConjugation |  禁止依存 661 本；KST.Spectra.PointedIntervalStrictConjugation → KST.Spectra.PointedIntervalConjugateSquare |
| R64 | KST.Spectra.PointedKanReplacement |  禁止依存 91 本；KST.Spectra.PointedKanReplacement → HA.Simplicial.AnodyneKanReplacement |
| R64 | KST.Spectra.PointedKanWhitehead |  禁止依存 110 本；KST.Spectra.PointedKanWhitehead → KST.Spectra.AcyclicFibrationLifting |
| R64 | KST.Spectra.PointedMappedIntervalTransposeStep |  禁止依存 625 本；KST.Spectra.PointedMappedIntervalTransposeStep → KST.Spectra.PointedIntervalNaturality |
| R64 | KST.Spectra.PointedMapping |  禁止依存 3 本；KST.Spectra.PointedMapping → Spectra.Pointed.InternalHom |
| R64 | KST.Spectra.PointedMappingComponents |  禁止依存 118 本；KST.Spectra.PointedMappingComponents → KST.Spectra.PointedMappingHomotopy |
| R64 | KST.Spectra.PointedMappingFamilyVertices |  禁止依存 116 本；KST.Spectra.PointedMappingFamilyVertices → KST.Spectra.PointedMappingParameters |
| R64 | KST.Spectra.PointedMappingHomotopy |  禁止依存 117 本；KST.Spectra.PointedMappingHomotopy → KST.Spectra.PointedMappingFamilyVertices |
| R64 | KST.Spectra.PointedMappingNaturality |  禁止依存 27 本；KST.Spectra.PointedMappingNaturality → KST.Spectra.SuspensionLoop |
| R64 | KST.Spectra.PointedMappingParameters |  禁止依存 28 本；KST.Spectra.PointedMappingParameters → KST.Spectra.PointedMappingNaturality |
| R64 | KST.Spectra.PointedParametricEvaluationTranspose |  禁止依存 620 本；KST.Spectra.PointedParametricEvaluationTranspose → KST.Spectra.PointedParametricPostExchange |
| R64 | KST.Spectra.PointedParametricPost |  禁止依存 614 本；KST.Spectra.PointedParametricPost → KST.Spectra.PointedIhomActionNaturality |
| R64 | KST.Spectra.PointedParametricPostCurry |  禁止依存 620 本；KST.Spectra.PointedParametricPostCurry → KST.Spectra.PointedParametricPostExchange |
| R64 | KST.Spectra.PointedParametricPostExchange |  禁止依存 619 本；KST.Spectra.PointedParametricPostExchange → KST.Spectra.PointedIhomParameterExchange |
| R64 | KST.Spectra.PointedParametricPostNaturality |  禁止依存 617 本；KST.Spectra.PointedParametricPostNaturality → KST.Spectra.PointedIhomActionSuspension |
| R64 | KST.Spectra.PointedPathProjectionContraction |  禁止依存 127 本；KST.Spectra.PointedPathProjectionContraction → HA.Simplicial.KanFibrationEndpointExtension |
| R64 | KST.Spectra.PointedPathSquareEndpointReflection |  禁止依存 630 本；KST.Spectra.PointedPathSquareEndpointReflection → KST.Spectra.PointedPathSquareReflection |
| R64 | KST.Spectra.PointedPathSquareReflection |  禁止依存 629 本；KST.Spectra.PointedPathSquareReflection → KST.Spectra.PointedConstantIntervalSquare |
| R64 | KST.Spectra.PointedPreActionComposition |  禁止依存 620 本；KST.Spectra.PointedPreActionComposition → KST.Spectra.PointedParametricPostExchange |
| R64 | KST.Spectra.PointedPreActionCotensor |  禁止依存 621 本；KST.Spectra.PointedPreActionCotensor → KST.Spectra.PointedPreActionComposition |
| R64 | KST.Spectra.PointedPrecompositionAction |  禁止依存 610 本；KST.Spectra.PointedPrecompositionAction → KST.Spectra.PointedPrecompositionInterval |
| R64 | KST.Spectra.PointedPrecompositionConstants |  禁止依存 617 本；KST.Spectra.PointedPrecompositionConstants → KST.Spectra.PointedPrecompositionSourceNaturality |
| R64 | KST.Spectra.PointedPrecompositionInterval |  禁止依存 609 本；KST.Spectra.PointedPrecompositionInterval → KST.Spectra.PointedRelativeTransposePaths |
| R64 | KST.Spectra.PointedPrecompositionNaturality |  禁止依存 611 本；KST.Spectra.PointedPrecompositionNaturality → KST.Spectra.PointedPrecompositionAction |
| R64 | KST.Spectra.PointedPrecompositionParametricNaturality |  禁止依存 659 本；KST.Spectra.PointedPrecompositionParametricNaturality → KST.Spectra.DeloopedExchangeSquareCoordinates |
| R64 | KST.Spectra.PointedPrecompositionSourceNaturality |  禁止依存 616 本；KST.Spectra.PointedPrecompositionSourceNaturality → KST.Spectra.PointedPrecompositionNaturality |
| R64 | KST.Spectra.PointedProjectedIhomPath |  禁止依存 642 本；KST.Spectra.PointedProjectedIhomPath → KST.Spectra.PointedIhomIntervalNaturality |
| R64 | KST.Spectra.PointedProjectionLoop |  禁止依存 610 本；KST.Spectra.PointedProjectionLoop → KST.Spectra.LoopTraceContraction |
| R64 | KST.Spectra.PointedPullbackChange |  禁止依存 95 本；KST.Spectra.PointedPullbackChange → KST.Spectra.PullbackKanSequence |
| R64 | KST.Spectra.PointedReedyWeightRestriction |  禁止依存 530 本；KST.Spectra.PointedReedyWeightRestriction → KST.Spectra.PointedWeightedEndUnderlyingWeight |
| R64 | KST.Spectra.PointedRelativeCofiberHomotopy |  禁止依存 133 本；KST.Spectra.PointedRelativeCofiberHomotopy → KST.Spectra.CofiberMappingFiberIso |
| R64 | KST.Spectra.PointedRelativeHomotopyAdjustment |  禁止依存 120 本；KST.Spectra.PointedRelativeHomotopyAdjustment → KST.Spectra.PointedHomotopyExtension |
| R64 | KST.Spectra.PointedRelativeTransposeHomotopy |  禁止依存 612 本；KST.Spectra.PointedRelativeTransposeHomotopy → KST.Spectra.PointedRelativeTransposePaths |
| R64 | KST.Spectra.PointedRelativeTransposePaths |  禁止依存 608 本；KST.Spectra.PointedRelativeTransposePaths → KST.Spectra.LoopMappingOperations |
| R64 | KST.Spectra.PointedRestrictionPathComposition |  禁止依存 618 本；KST.Spectra.PointedRestrictionPathComposition → KST.Spectra.FibrationEdgeComposition |
| R64 | KST.Spectra.PointedRlpSection |  禁止依存 612 本；KST.Spectra.PointedRlpSection → HA.Simplicial.MonoRightLiftingRelativeHomotopy |
| R64 | KST.Spectra.PointedSequence |  禁止依存 27 本；KST.Spectra.PointedSequence → KST.Spectra.SuspensionLoop |
| R64 | KST.Spectra.PointedSkeletalMappingTower |  禁止依存 436 本；KST.Spectra.PointedSkeletalMappingTower → KST.Spectra.ConstantPointedHomotopyEnd |
| R64 | KST.Spectra.PointedSmallProduct |  禁止依存 63 本；KST.Spectra.PointedSmallProduct → KST.Spectra.PointedGroupProduct |
| R64 | KST.Spectra.PointedSmashExchange |  禁止依存 28 本；KST.Spectra.PointedSmashExchange → Spectra.PointedSimplicialSet.SmashUnderlyingCoherence |
| R64 | KST.Spectra.PointedSpectrumIntervalTranspose |  禁止依存 619 本；KST.Spectra.PointedSpectrumIntervalTranspose → KST.Spectra.PointedIhomStepInterval |
| R64 | KST.Spectra.PointedStandardEndComparison |  禁止依存 565 本；KST.Spectra.PointedStandardEndComparison → KST.Spectra.PointedTotalizationEndIso |
| R64 | KST.Spectra.PointedTotalization |  禁止依存 178 本；KST.Spectra.PointedTotalization → KST.Spectra.CosimplicialTotalization |
| R64 | KST.Spectra.PointedTotalizationBousfieldKan |  禁止依存 512 本；KST.Spectra.PointedTotalizationBousfieldKan → KST.Spectra.PointedHomotopyLimit |
| R64 | KST.Spectra.PointedTotalizationComparisonPi |  禁止依存 556 本；KST.Spectra.PointedTotalizationComparisonPi → KST.Spectra.PointedTotalizationBousfieldKan |
| R64 | KST.Spectra.PointedTotalizationEndIso |  禁止依存 564 本；KST.Spectra.PointedTotalizationEndIso → KST.Spectra.PointedTotalizationComparisonPi |
| R64 | KST.Spectra.PointedTowerDifferential |  禁止依存 115 本；KST.Spectra.PointedTowerDifferential → KST.Spectra.PointedFibrationBoundary |
| R64 | KST.Spectra.PointedTowerDifferentialNaturality |  禁止依存 118 本；KST.Spectra.PointedTowerDifferentialNaturality → KST.Spectra.PointedFibrationNaturality |
| R64 | KST.Spectra.PointedTowerLoopDifferential |  禁止依存 138 本；KST.Spectra.PointedTowerLoopDifferential → KST.Spectra.LoopConnectingAnticommutation |
| R64 | KST.Spectra.PointedTowerRepresentatives |  禁止依存 63 本；KST.Spectra.PointedTowerRepresentatives → KST.Spectra.PointedGroupProduct |
| R64 | KST.Spectra.PointedTowerZeroDifferential |  禁止依存 141 本；KST.Spectra.PointedTowerZeroDifferential → KST.Spectra.PointedHomotopy |
| R64 | KST.Spectra.PointedTracedPathBoundary |  禁止依存 609 本；KST.Spectra.PointedTracedPathBoundary → KST.Spectra.PointedTracedPathLift |
| R64 | KST.Spectra.PointedTracedPathLift |  禁止依存 608 本；KST.Spectra.PointedTracedPathLift → HA.HomotopyFunctionComplex.BoundaryOne |
| R64 | KST.Spectra.PointedTracedPathSquare |  禁止依存 635 本；KST.Spectra.PointedTracedPathSquare → KST.Spectra.FreePathEvaluation |
| R64 | KST.Spectra.PointedTransposeIntervalRestriction |  禁止依存 615 本；KST.Spectra.PointedTransposeIntervalRestriction → KST.Spectra.PointedBasedPathComposition |
| R64 | KST.Spectra.PointedTransposeRestrictions |  禁止依存 122 本；KST.Spectra.PointedTransposeRestrictions → KST.Spectra.PointedHomTransposeComponents |
| R64 | KST.Spectra.PointedTrivialVerticalPaths |  禁止依存 122 本；KST.Spectra.PointedTrivialVerticalPaths → KST.Spectra.PointedKanWhitehead |
| R64 | KST.Spectra.PointedUnitMappingFamily |  禁止依存 140 本；KST.Spectra.PointedUnitMappingFamily → KST.Spectra.PointedExchangeVertices |
| R64 | KST.Spectra.PointedVertexComparison |  禁止依存 117 本；KST.Spectra.PointedVertexComparison → KST.Spectra.PointedMappingFamilyVertices |
| R64 | KST.Spectra.PointedVerticalChainCompression |  禁止依存 606 本；KST.Spectra.PointedVerticalChainCompression → KST.Spectra.PointedVerticalPathFiber |
| R64 | KST.Spectra.PointedVerticalChainExtension |  禁止依存 605 本；KST.Spectra.PointedVerticalChainExtension → KST.Spectra.PointedRelativeHomotopyAdjustment |
| R64 | KST.Spectra.PointedVerticalChains |  禁止依存 603 本；KST.Spectra.PointedVerticalChains → KST.Spectra.PointedVerticalPathFunctoriality |
| R64 | KST.Spectra.PointedVerticalPathComposition |  禁止依存 608 本；KST.Spectra.PointedVerticalPathComposition → KST.Spectra.FibrationCompositionTriangleLift |
| R64 | KST.Spectra.PointedVerticalPathFiber |  禁止依存 604 本；KST.Spectra.PointedVerticalPathFiber → KST.Spectra.PointedVerticalChains |
| R64 | KST.Spectra.PointedVerticalPathFunctoriality |  禁止依存 602 本；KST.Spectra.PointedVerticalPathFunctoriality → KST.Spectra.PointedVerticalPaths |
| R64 | KST.Spectra.PointedVerticalPaths |  禁止依存 121 本；KST.Spectra.PointedVerticalPaths → KST.Spectra.PointedHomotopyClasses |
| R64 | KST.Spectra.PointedWeightedCone |  禁止依存 420 本；KST.Spectra.PointedWeightedCone → KST.Spectra.PointedWeightedEndCotensor |
| R64 | KST.Spectra.PointedWeightedConeCompatibility |  禁止依存 421 本；KST.Spectra.PointedWeightedConeCompatibility → KST.Spectra.PointedWeightedCone |
| R64 | KST.Spectra.PointedWeightedConePreMap |  禁止依存 424 本；KST.Spectra.PointedWeightedConePreMap → KST.Spectra.PointedWeightedCone |
| R64 | KST.Spectra.PointedWeightedConeUnderlying |  禁止依存 423 本；KST.Spectra.PointedWeightedConeUnderlying → KST.Spectra.PointedVertexComparison |
| R64 | KST.Spectra.PointedWeightedEnd |  禁止依存 416 本；KST.Spectra.PointedWeightedEnd → KST.Spectra.EndRightAdjoint |
| R64 | KST.Spectra.PointedWeightedEndBasepoint |  禁止依存 418 本；KST.Spectra.PointedWeightedEndBasepoint → KST.Spectra.PointedWeightedEndMap |
| R64 | KST.Spectra.PointedWeightedEndBifunctor |  禁止依存 424 本；KST.Spectra.PointedWeightedEndBifunctor → KST.Spectra.PointedWeightedEndPreMap |
| R64 | KST.Spectra.PointedWeightedEndCotensor |  禁止依存 418 本；KST.Spectra.PointedWeightedEndCotensor → KST.Spectra.EndInternalHom |
| R64 | KST.Spectra.PointedWeightedEndCotensorWeight |  禁止依存 424 本；KST.Spectra.PointedWeightedEndCotensorWeight → KST.Spectra.PointedWeightedConeCompatibility |
| R64 | KST.Spectra.PointedWeightedEndFunctor |  禁止依存 422 本；KST.Spectra.PointedWeightedEndFunctor → KST.Spectra.PointedWeightedConeCompatibility |
| R64 | KST.Spectra.PointedWeightedEndMap |  禁止依存 417 本；KST.Spectra.PointedWeightedEndMap → KST.Spectra.PointedWeightedEnd |
| R64 | KST.Spectra.PointedWeightedEndPreMap |  禁止依存 423 本；KST.Spectra.PointedWeightedEndPreMap → KST.Spectra.PointedWeightedEndFunctor |
| R64 | KST.Spectra.PointedWeightedEndUnderlyingWeight |  禁止依存 424 本；KST.Spectra.PointedWeightedEndUnderlyingWeight → IC.HomotopyLimits.WeightedRestriction |
| R64 | KST.Spectra.PointedWeightedEndWeightFunctor |  禁止依存 425 本；KST.Spectra.PointedWeightedEndWeightFunctor → KST.Spectra.PointedWeightedEndBifunctor |
| R64 | KST.Spectra.PointedWeightedEndWeightLimits |  禁止依存 425 本；KST.Spectra.PointedWeightedEndWeightLimits → KST.Spectra.EndLimitPreservation |
| R64 | KST.Spectra.PointedZeroConnecting |  禁止依存 119 本；KST.Spectra.PointedZeroConnecting → KST.Spectra.LoopZeroPenultimate |
| R64 | KST.Spectra.PointedZeroConnectingNaturality |  禁止依存 121 本；KST.Spectra.PointedZeroConnectingNaturality → KST.Spectra.PointedFiberComparison |
| R64 | KST.Spectra.PointedZeroMapping |  禁止依存 29 本；KST.Spectra.PointedZeroMapping → KST.Spectra.PointedMappingParameters |
| R64 | KST.Spectra.PostMappingFibration |  禁止依存 62 本；KST.Spectra.PostMappingFibration → KST.Spectra.PostMappingLifts |
| R64 | KST.Spectra.PostMappingIsomorphism |  禁止依存 115 本；KST.Spectra.PostMappingIsomorphism → KST.Spectra.PointedKanWhitehead |
| R64 | KST.Spectra.PostMappingLifts |  禁止依存 61 本；KST.Spectra.PostMappingLifts → HA.Simplicial.RelativeProductLifting |
| R27 | KST.Spectra.PullbackKanSequence | R27 の汎用17本の外：Ωスペクトル・構造射付き列に固有。呼出元の上方移動も規則8(b)で保留。 禁止依存 94 本；KST.Spectra.PullbackKanSequence → KST.Spectra.KanSequence |
| R64 | KST.Spectra.SkeletalAdditiveCoefficientDifferential |  禁止依存 634 本；KST.Spectra.SkeletalAdditiveCoefficientDifferential → KST.Spectra.SkeletalCoefficientAlternating |
| R64 | KST.Spectra.SkeletalCellBoundaryRepresentatives |  禁止依存 566 本；KST.Spectra.SkeletalCellBoundaryRepresentatives → KST.Spectra.RestrictionConnectingNullhomotopy |
| R64 | KST.Spectra.SkeletalCellBoundaryRestriction |  禁止依存 560 本；KST.Spectra.SkeletalCellBoundaryRestriction → KST.Spectra.CellMappingCoordinates |
| R64 | KST.Spectra.SkeletalCellCofiber |  禁止依存 445 本；KST.Spectra.SkeletalCellCofiber → KST.Spectra.PointedCofiberPushout |
| R64 | KST.Spectra.SkeletalCellConnecting |  禁止依存 561 本；KST.Spectra.SkeletalCellConnecting → KST.Spectra.SkeletalCellBoundaryRestriction |
| R64 | KST.Spectra.SkeletalCellFiberNaturality |  禁止依存 474 本；KST.Spectra.SkeletalCellFiberNaturality → KST.Spectra.SkeletalCellCofiber |
| R64 | KST.Spectra.SkeletalCoefficientAlternating |  禁止依存 633 本；KST.Spectra.SkeletalCoefficientAlternating → KST.Spectra.SkeletalCoefficientAlternatingZero |
| R64 | KST.Spectra.SkeletalCoefficientAlternatingAll |  禁止依存 642 本；KST.Spectra.SkeletalCoefficientAlternatingAll → KST.Spectra.SkeletalCoefficientAlternating |
| R64 | KST.Spectra.SkeletalCoefficientAlternatingZero |  禁止依存 631 本；KST.Spectra.SkeletalCoefficientAlternatingZero → KST.Spectra.SkeletalDoubleLoopDifferential |
| R64 | KST.Spectra.SkeletalCoefficientDifferential |  禁止依存 528 本；KST.Spectra.SkeletalCoefficientDifferential → KST.Spectra.SkeletalFiberCoefficientGroups |
| R64 | KST.Spectra.SkeletalCoefficientDifferentialNaturality |  禁止依存 554 本；KST.Spectra.SkeletalCoefficientDifferentialNaturality → KST.Spectra.SkeletalCoefficientDifferential |
| R64 | KST.Spectra.SkeletalCoefficientExactness |  禁止依存 649 本；KST.Spectra.SkeletalCoefficientExactness → KST.Spectra.NormalizedValueCochainExactness |
| R64 | KST.Spectra.SkeletalCoefficientLoopDifferential |  禁止依存 588 本；KST.Spectra.SkeletalCoefficientLoopDifferential → KST.Spectra.SkeletalCoefficientDifferential |
| R64 | KST.Spectra.SkeletalCoefficientNaturality |  禁止依存 552 本；KST.Spectra.SkeletalCoefficientNaturality → KST.Spectra.SimplexCellPositiveNaturality |
| R64 | KST.Spectra.SkeletalConnectingAlternating |  禁止依存 593 本；KST.Spectra.SkeletalConnectingAlternating → KST.Spectra.SkeletalPathAlternating |
| R64 | KST.Spectra.SkeletalDoubleLoopDifferential |  禁止依存 630 本；KST.Spectra.SkeletalDoubleLoopDifferential → KST.Spectra.NormalizedValueNaturality |
| R64 | KST.Spectra.SkeletalEdgeAlternating |  禁止依存 627 本；KST.Spectra.SkeletalEdgeAlternating → KST.Spectra.SkeletalEdgeConnecting |
| R64 | KST.Spectra.SkeletalEdgeCochain |  禁止依存 520 本；KST.Spectra.SkeletalEdgeCochain → KST.Spectra.LoopFundamentalCommutativity |
| R64 | KST.Spectra.SkeletalEdgeConnecting |  禁止依存 595 本；KST.Spectra.SkeletalEdgeConnecting → KST.Spectra.ReverseComponentConnecting |
| R64 | KST.Spectra.SkeletalEdgeDoubleLoop |  禁止依存 631 本；KST.Spectra.SkeletalEdgeDoubleLoop → KST.Spectra.NormalizedValueNaturality |
| R64 | KST.Spectra.SkeletalEdgePath |  禁止依存 583 本；KST.Spectra.SkeletalEdgePath → KST.Spectra.LoopBoundaryRepresentatives |
| R64 | KST.Spectra.SkeletalFiberAbelian |  禁止依存 529 本；KST.Spectra.SkeletalFiberAbelian → KST.Spectra.SkeletalCoefficientDifferential |
| R64 | KST.Spectra.SkeletalFiberCoefficientGroups |  禁止依存 517 本；KST.Spectra.SkeletalFiberCoefficientGroups → KST.Spectra.SimplexCellHomotopyGroups |
| R64 | KST.Spectra.SkeletalFiberComponents |  禁止依存 506 本；KST.Spectra.SkeletalFiberComponents → KST.Spectra.FunctionComplexComponents |
| R64 | KST.Spectra.SkeletalFiberDifferential |  禁止依存 465 本；KST.Spectra.SkeletalFiberDifferential → KST.Spectra.PointedTowerDifferential |
| R64 | KST.Spectra.SkeletalFiberDifferentialNaturality |  禁止依存 469 本；KST.Spectra.SkeletalFiberDifferentialNaturality → KST.Spectra.PointedTowerDifferentialNaturality |
| R64 | KST.Spectra.SkeletalFiberExactness |  禁止依存 652 本；KST.Spectra.SkeletalFiberExactness → KST.Spectra.SkeletalCoefficientExactness |
| R64 | KST.Spectra.SkeletalFiberFunctions |  禁止依存 499 本；KST.Spectra.SkeletalFiberFunctions → KST.Spectra.PointedCoproductHom |
| R64 | KST.Spectra.SkeletalFiberLoopCoefficients |  禁止依存 557 本；KST.Spectra.SkeletalFiberLoopCoefficients → KST.Spectra.CellMappingCoordinates |
| R64 | KST.Spectra.SkeletalFiberLoopPositive |  禁止依存 560 本；KST.Spectra.SkeletalFiberLoopPositive → KST.Spectra.SimplexCellLoopPositive |
| R64 | KST.Spectra.SkeletalFiberLoopZero |  禁止依存 601 本；KST.Spectra.SkeletalFiberLoopZero → KST.Spectra.SimplexCellZeroLoop |
| R64 | KST.Spectra.SkeletalFiberRepresentatives |  禁止依存 514 本；KST.Spectra.SkeletalFiberRepresentatives → KST.Spectra.CellMappingVertices |
| R64 | KST.Spectra.SkeletalFirstFiber |  禁止依存 652 本；KST.Spectra.SkeletalFirstFiber → KST.Spectra.NormalizedFirstCocycles |
| R64 | KST.Spectra.SkeletalFunctionNaturality |  禁止依存 520 本；KST.Spectra.SkeletalFunctionNaturality → KST.Spectra.PointedCoproductHomNaturality |
| R64 | KST.Spectra.SkeletalInitialDetection |  禁止依存 687 本；KST.Spectra.SkeletalInitialDetection → KST.Spectra.SkeletalFirstFiber |
| R64 | KST.Spectra.SkeletalLoopAlternating |  禁止依存 625 本；KST.Spectra.SkeletalLoopAlternating → KST.Spectra.SkeletalConnectingAlternating |
| R64 | KST.Spectra.SkeletalLoopDifferential |  禁止依存 586 本；KST.Spectra.SkeletalLoopDifferential → KST.Spectra.PointedTowerDifferentialNaturality |
| R64 | KST.Spectra.SkeletalLoopFiberIso |  禁止依存 563 本；KST.Spectra.SkeletalLoopFiberIso → KST.Spectra.PositiveLoopNaturality |
| R64 | KST.Spectra.SkeletalLoopInput |  禁止依存 619 本；KST.Spectra.SkeletalLoopInput → KST.Spectra.SkeletalCellBoundaryRestriction |
| R64 | KST.Spectra.SkeletalMapSimplex |  禁止依存 515 本；KST.Spectra.SkeletalMapSimplex → KST.Spectra.SkeletalFiberRepresentatives |
| R64 | KST.Spectra.SkeletalMappingDetection |  禁止依存 681 本；KST.Spectra.SkeletalMappingDetection → KST.Spectra.SkeletalMappingGroupComparison |
| R64 | KST.Spectra.SkeletalMappingFiber |  禁止依存 443 本；KST.Spectra.SkeletalMappingFiber → KST.Spectra.UnbasedMappingFiberIso |
| R64 | KST.Spectra.SkeletalMappingGroupComparison |  禁止依存 679 本；KST.Spectra.SkeletalMappingGroupComparison → KST.Spectra.SkeletalMappingLimitIso |
| R64 | KST.Spectra.SkeletalMappingLimitIso |  禁止依存 440 本；KST.Spectra.SkeletalMappingLimitIso → KST.Spectra.PointedSkeletalMappingTower |
| R64 | KST.Spectra.SkeletalMappingTower |  禁止依存 426 本；KST.Spectra.SkeletalMappingTower → KST.Spectra.SkeletalWeightColimit |
| R64 | KST.Spectra.SkeletalPathAlternating |  禁止依存 540 本；KST.Spectra.SkeletalPathAlternating → KST.Spectra.SkeletalPathCoboundary |
| R64 | KST.Spectra.SkeletalPathCoboundary |  禁止依存 539 本；KST.Spectra.SkeletalPathCoboundary → KST.Spectra.LoopBoundaryRepresentatives |
| R64 | KST.Spectra.SkeletalPathConnecting |  禁止依存 591 本；KST.Spectra.SkeletalPathConnecting → KST.Spectra.ReverseComponentConnecting |
| R64 | KST.Spectra.SkeletalPositiveAdditiveDifferential |  禁止依存 644 本；KST.Spectra.SkeletalPositiveAdditiveDifferential → KST.Spectra.SkeletalAdditiveCoefficientDifferential |
| R64 | KST.Spectra.SkeletalRelativeRepresentatives |  禁止依存 509 本；KST.Spectra.SkeletalRelativeRepresentatives → KST.Spectra.CellCofiberProjections |
| R64 | KST.Spectra.SkeletalSphericalComponents |  禁止依存 507 本；KST.Spectra.SkeletalSphericalComponents → KST.Spectra.SkeletalFiberComponents |
| R64 | KST.Spectra.SkeletalStandardLatching |  禁止依存 100 本；KST.Spectra.SkeletalStandardLatching → KST.Spectra.BousfieldKanWeightLatching |
| R64 | KST.Spectra.SkeletalStrictRealization |  禁止依存 515 本；KST.Spectra.SkeletalStrictRealization → KST.Spectra.SkeletalFiberRepresentatives |
| R64 | KST.Spectra.SkeletalTowerMittagLeffler |  禁止依存 677 本；KST.Spectra.SkeletalTowerMittagLeffler → KST.Spectra.SkeletalFiberExactness |
| R64 | KST.Spectra.SkeletalTransitionLatchingPullback |  禁止依存 102 本；KST.Spectra.SkeletalTransitionLatchingPullback → KST.Spectra.SkeletalStandardLatching |
| R64 | KST.Spectra.SkeletalTransitionReedyMono |  禁止依存 103 本；KST.Spectra.SkeletalTransitionReedyMono → KST.Spectra.SkeletalTransitionLatchingPullback |
| R64 | KST.Spectra.SkeletalWeightColimit |  禁止依存 425 本；KST.Spectra.SkeletalWeightColimit → KST.Spectra.SkeletalWeightedEndTower |
| R64 | KST.Spectra.SkeletalWeightedEndLimit |  禁止依存 428 本；KST.Spectra.SkeletalWeightedEndLimit → KST.Spectra.PointedWeightedEndWeightLimits |
| R64 | KST.Spectra.SkeletalWeightedEndTower |  禁止依存 424 本；KST.Spectra.SkeletalWeightedEndTower → KST.Spectra.PointedWeightedEndPreMap |
| R64 | KST.Spectra.SkeletalZeroCellConnecting |  禁止依存 600 本；KST.Spectra.SkeletalZeroCellConnecting → KST.Spectra.RestrictionZeroConnecting |
| R64 | KST.Spectra.SkeletalZeroCellRepresentatives |  禁止依存 601 本；KST.Spectra.SkeletalZeroCellRepresentatives → KST.Spectra.SkeletalZeroCellConnecting |
| R64 | KST.Spectra.SkeletalZeroCoefficientDifferential |  禁止依存 603 本；KST.Spectra.SkeletalZeroCoefficientDifferential → KST.Spectra.SkeletalCoefficientDifferential |
| R64 | KST.Spectra.SkeletalZeroComponents |  禁止依存 590 本；KST.Spectra.SkeletalZeroComponents → KST.Spectra.SkeletalZeroDifferential |
| R64 | KST.Spectra.SkeletalZeroDifferential |  禁止依存 589 本；KST.Spectra.SkeletalZeroDifferential → KST.Spectra.PointedTowerZeroDifferential |
| R64 | KST.Spectra.SmashSmallProductMono |  禁止依存 109 本；KST.Spectra.SmashSmallProductMono → IC.HomotopyLimits.SmashProductMono |
| R64 | KST.Spectra.SmashSmallProductSimplex |  禁止依存 105 本；KST.Spectra.SmashSmallProductSimplex → IC.HomotopyLimits.SmashSimplex |
| R64 | KST.Spectra.SpectrumHomotopyFunctor |  禁止依存 60 本；KST.Spectra.SpectrumHomotopyFunctor → KST.Spectra.SpectrumHomotopyGroups |
| R64 | KST.Spectra.SpectrumHomotopyGroups |  禁止依存 59 本；KST.Spectra.SpectrumHomotopyGroups → KST.Spectra.OmegaSpectrumZeroGroups |
| R64 | KST.Spectra.SpectrumMorphisms |  禁止依存 31 本；KST.Spectra.SpectrumMorphisms → KST.Spectra.OmegaSpectrum |
| R64 | KST.Spectra.SphericalPathBoundary |  禁止依存 52 本；KST.Spectra.SphericalPathBoundary → KST.Spectra.LoopHomotopyGroups |
| R64 | KST.Spectra.SquareBoundaryEdges |  禁止依存 114 本；KST.Spectra.SquareBoundaryEdges → KST.Spectra.TriangleDiskFaces |
| R64 | KST.Spectra.SquareBoundaryFamilies |  禁止依存 130 本；KST.Spectra.SquareBoundaryFamilies → KST.Spectra.IntervalBoundaryFamilies |
| R64 | KST.Spectra.SquareTriangleRestriction |  禁止依存 115 本；KST.Spectra.SquareTriangleRestriction → KST.Spectra.SquareBoundaryEdges |
| R64 | KST.Spectra.SuspensionComposition |  禁止依存 38 本；KST.Spectra.SuspensionComposition → KST.Spectra.PointedEnrichment |
| R64 | KST.Spectra.SuspensionLoop |  禁止依存 26 本；KST.Spectra.SuspensionLoop → KST.Spectra.PointedMapping |
| R64 | KST.Spectra.ThreeEdgeTransportSquare |  禁止依存 125 本；KST.Spectra.ThreeEdgeTransportSquare → KST.Spectra.FibrationEdgeComposition |
| R64 | KST.Spectra.ThreeEdgeTransportSquareProjection |  禁止依存 126 本；KST.Spectra.ThreeEdgeTransportSquareProjection → KST.Spectra.ThreeEdgeTransportSquare |
| R64 | KST.Spectra.TowerCompatibleDetection |  禁止依存 121 本；KST.Spectra.TowerCompatibleDetection → KST.Spectra.TowerDifferentialCorrection |
| R64 | KST.Spectra.TowerCompatibleHomotopies |  禁止依存 107 本；KST.Spectra.TowerCompatibleHomotopies → KST.Spectra.TowerHomotopyTriangleStep |
| R64 | KST.Spectra.TowerDifferenceRealization |  禁止依存 104 本；KST.Spectra.TowerDifferenceRealization → KST.Spectra.TowerDifferenceRealizationStep |
| R64 | KST.Spectra.TowerDifferenceRealizationStep |  禁止依存 103 本；KST.Spectra.TowerDifferenceRealizationStep → KST.Spectra.NullDifferenceRealization |
| R64 | KST.Spectra.TowerDifferentialCorrection |  禁止依存 117 本；KST.Spectra.TowerDifferentialCorrection → KST.Spectra.PointedFibrationExactness |
| R64 | KST.Spectra.TowerGroupLimitComparison |  禁止依存 65 本；KST.Spectra.TowerGroupLimitComparison → KST.Spectra.TowerHomotopyComparison |
| R64 | KST.Spectra.TowerHomotopyComparison |  禁止依存 64 本；KST.Spectra.TowerHomotopyComparison → KST.Spectra.PointedTowerRepresentatives |
| R64 | KST.Spectra.TowerHomotopyTriangleStep |  禁止依存 106 本；KST.Spectra.TowerHomotopyTriangleStep → KST.Spectra.NullHomotopyTriangleLifting |
| R64 | KST.Spectra.TowerInitialDetection |  禁止依存 122 本；KST.Spectra.TowerInitialDetection → KST.Spectra.TowerCompatibleDetection |
| R64 | KST.Spectra.TowerKernelLimOneEquiv |  禁止依存 123 本；KST.Spectra.TowerKernelLimOneEquiv → KST.Spectra.TowerKernelObstructionInjective |
| R64 | KST.Spectra.TowerKernelNullCriterion |  禁止依存 112 本；KST.Spectra.TowerKernelNullCriterion → KST.Spectra.TowerKernelObstruction |
| R64 | KST.Spectra.TowerKernelObstruction |  禁止依存 105 本；KST.Spectra.TowerKernelObstruction → KST.Spectra.TowerKernelRepresentativeObstruction |
| R64 | KST.Spectra.TowerKernelObstructionInjective |  禁止依存 118 本；KST.Spectra.TowerKernelObstructionInjective → KST.Spectra.TowerCompatibleHomotopies |
| R64 | KST.Spectra.TowerKernelObstructionSurjective |  禁止依存 113 本；KST.Spectra.TowerKernelObstructionSurjective → KST.Spectra.TowerDifferenceRealization |
| R64 | KST.Spectra.TowerKernelRealization |  禁止依存 106 本；KST.Spectra.TowerKernelRealization → KST.Spectra.TowerKernelObstruction |
| R64 | KST.Spectra.TowerKernelRepresentativeObstruction |  禁止依存 102 本；KST.Spectra.TowerKernelRepresentativeObstruction → KST.Spectra.TowerGroupLimitComparison |
| R64 | KST.Spectra.TowerMilnorConvergence |  禁止依存 127 本；KST.Spectra.TowerMilnorConvergence → KST.Spectra.TowerKernelNullCriterion |
| R64 | KST.Spectra.TowerMilnorExactness |  禁止依存 124 本；KST.Spectra.TowerMilnorExactness → KST.Spectra.TowerKernelLimOneEquiv |
| R64 | KST.Spectra.TowerMittagLefflerComparison |  禁止依存 113 本；KST.Spectra.TowerMittagLefflerComparison → KST.Spectra.TowerKernelNullCriterion |
| R64 | KST.Spectra.TowerNullHomotopyNormalization |  禁止依存 100 本；KST.Spectra.TowerNullHomotopyNormalization → KST.Spectra.NullDifferenceRealization |
| R64 | KST.Spectra.TowerNullHomotopyObstruction |  禁止依存 98 本；KST.Spectra.TowerNullHomotopyObstruction → KST.Spectra.NullHomotopyDifferenceChange |
| R64 | KST.Spectra.TowerObstructionAlignment |  禁止依存 101 本；KST.Spectra.TowerObstructionAlignment → KST.Spectra.TowerNullHomotopyNormalization |
| R64 | KST.Spectra.TowerObstructionTransport |  禁止依存 100 本；KST.Spectra.TowerObstructionTransport → KST.Spectra.NullTransportDifference |
| R64 | KST.Spectra.TowerRelativeHomotopyLimit |  禁止依存 65 本；KST.Spectra.TowerRelativeHomotopyLimit → KST.Spectra.TowerHomotopyComparison |
| R64 | KST.Spectra.TowerStrictNullHomotopies |  禁止依存 103 本；KST.Spectra.TowerStrictNullHomotopies → KST.Spectra.NullHomotopyStrictLifting |
| R64 | KST.Spectra.TowerTwoStepRanges |  禁止依存 114 本；KST.Spectra.TowerTwoStepRanges → KST.Spectra.TowerMittagLefflerComparison |
| R64 | KST.Spectra.TruncatedMapping |  禁止依存 4 本；KST.Spectra.TruncatedMapping → KST.Spectra.PointedMapping |
| R64 | KST.Spectra.ZeroConnectingInjectivity |  禁止依存 44 本；KST.Spectra.ZeroConnectingInjectivity → KST.Spectra.BoundaryFilling |
| R64 | Spectra.Pointed.AdjoinBasepoint | 衝突：Spectra.Pointed.AdjoinBasepoint, Spectra.PointedSimplicialSet.AdjoinBasepoint |
| R64 | Spectra.Pointed.AdjoinBasepointProduct | 衝突：Spectra.Pointed.AdjoinBasepointProduct, Spectra.PointedSimplicialSet.AdjoinBasepointProduct |
| R64 | Spectra.Pointed.Basic | 衝突：Spectra.Pointed.Basic, Spectra.PointedSimplicialSet.Basic |
| R64 | Spectra.Pointed.Cofiber |  禁止依存 1 本；Spectra.Pointed.Cofiber → Spectra.Pointed.Basic |
| R64 | Spectra.Pointed.CofiberPushout |  禁止依存 3 本；Spectra.Pointed.CofiberPushout → Spectra.Pointed.AdjoinBasepoint |
| R64 | Spectra.Pointed.InternalHom | 衝突：Spectra.Pointed.InternalHom, Spectra.PointedSimplicialSet.InternalHom |
| R64 | Spectra.Pointed.ProductAssociator |  禁止依存 2 本；Spectra.Pointed.ProductAssociator → Spectra.Pointed.Products |
| R64 | Spectra.Pointed.ProductColimits |  禁止依存 7 本；Spectra.Pointed.ProductColimits → Spectra.Pointed.SmashUnit |
| R64 | Spectra.Pointed.Products |  禁止依存 1 本；Spectra.Pointed.Products → Spectra.Pointed.Basic |
| R64 | Spectra.Pointed.ReducedPair |  禁止依存 3 本；Spectra.Pointed.ReducedPair → Spectra.Pointed.Smash |
| R64 | Spectra.Pointed.Smash |  禁止依存 2 本；Spectra.Pointed.Smash → Spectra.Pointed.Products |
| R64 | Spectra.Pointed.SmashAdjunction |  禁止依存 7 本；Spectra.Pointed.SmashAdjunction → Spectra.Pointed.SmashCurrying |
| R64 | Spectra.Pointed.SmashAssociator |  禁止依存 10 本；Spectra.Pointed.SmashAssociator → Spectra.Pointed.TripleSmash |
| R64 | Spectra.Pointed.SmashCurrying |  禁止依存 5 本；Spectra.Pointed.SmashCurrying → Spectra.Pointed.InternalHom |
| R64 | Spectra.Pointed.SmashHexagon |  禁止依存 11 本；Spectra.Pointed.SmashHexagon → Spectra.Pointed.SmashAssociator |
| R64 | Spectra.Pointed.SmashMonoidal |  禁止依存 18 本；Spectra.Pointed.SmashMonoidal → Spectra.Pointed.SmashAdjunction |
| R64 | Spectra.Pointed.SmashPentagon |  禁止依存 11 本；Spectra.Pointed.SmashPentagon → Spectra.Pointed.SmashAssociator |
| R64 | Spectra.Pointed.SmashPushoutProduct |  禁止依存 3 本；Spectra.Pointed.SmashPushoutProduct → Spectra.Pointed.Smash |
| R64 | Spectra.Pointed.SmashSymmetry |  禁止依存 3 本；Spectra.Pointed.SmashSymmetry → Spectra.Pointed.Smash |
| R64 | Spectra.Pointed.SmashTriangle |  禁止依存 11 本；Spectra.Pointed.SmashTriangle → Spectra.Pointed.SmashAssociator |
| R64 | Spectra.Pointed.SmashUnit |  禁止依存 6 本；Spectra.Pointed.SmashUnit → Spectra.Pointed.AdjoinBasepoint |
| R64 | Spectra.Pointed.TensorCoproduct |  禁止依存 1 本；Spectra.Pointed.TensorCoproduct → Spectra.Pointed.Basic |
| R64 | Spectra.Pointed.TripleSmash |  禁止依存 9 本；Spectra.Pointed.TripleSmash → Spectra.Pointed.ProductAssociator |
| R64 | Spectra.PointedSimplicialSet.AdjoinBasepoint | 衝突：Spectra.Pointed.AdjoinBasepoint, Spectra.PointedSimplicialSet.AdjoinBasepoint |
| R64 | Spectra.PointedSimplicialSet.AdjoinBasepointProduct | 衝突：Spectra.Pointed.AdjoinBasepointProduct, Spectra.PointedSimplicialSet.AdjoinBasepointProduct |
| R64 | Spectra.PointedSimplicialSet.AdjoinBasepointUnit |  禁止依存 26 本；Spectra.PointedSimplicialSet.AdjoinBasepointUnit → Spectra.PointedSimplicialSet.AdjoinBasepoint |
| R64 | Spectra.PointedSimplicialSet.Basic | 衝突：Spectra.Pointed.Basic, Spectra.PointedSimplicialSet.Basic |
| R64 | Spectra.PointedSimplicialSet.InternalHom | 衝突：Spectra.Pointed.InternalHom, Spectra.PointedSimplicialSet.InternalHom |
| R64 | Spectra.PointedSimplicialSet.Monoidal |  禁止依存 24 本；Spectra.PointedSimplicialSet.Monoidal → Spectra.Pointed.SmashMonoidal |
| R64 | Spectra.PointedSimplicialSet.MonoidalPrerequisites |  禁止依存 16 本；Spectra.PointedSimplicialSet.MonoidalPrerequisites → Spectra.Pointed.SmashHexagon |
| R64 | Spectra.PointedSimplicialSet.SmashUnderlying |  禁止依存 25 本；Spectra.PointedSimplicialSet.SmashUnderlying → Spectra.PointedSimplicialSet.Monoidal |
| R64 | Spectra.PointedSimplicialSet.SmashUnderlyingCoherence |  禁止依存 27 本；Spectra.PointedSimplicialSet.SmashUnderlyingCoherence → CategoryTheory.Monoidal.LaxPointHom |
| R64 | Spectra.PointedSimplicialSet.Spheres |  禁止依存 4 本；Spectra.PointedSimplicialSet.Spheres → Spectra.Pointed.AdjoinBasepoint |

## 待機事項

DG-W1 取り込みの通知と、R79・R75 を同じ束に含める案の確認を待つ。今回の w2a.json を実行済み・検収済みとして扱わない。IF-W0-4 では merge_modules.py・build lock・warm-up は DG 側の担当とし、∞ 側の残りは R75、CategoryTheory/Coxeter の基盤登録、監査 RSS を使うメモリ予算つき並列化である。
