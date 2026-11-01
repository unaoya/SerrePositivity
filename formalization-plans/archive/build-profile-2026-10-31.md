# ビルドの計測（2026-10-31 の main の全ビルドから）

概要：区切り 1-3 ＋ DG-W1 の後の main（194a65110）を 19:17〜21:26 に全ビルドしたログ（27,854 ジョブ、新規 10,660 本）から、モジュールごとのエラボレート時間を集計した。重いモジュールの整理（∞ 計画 R80、DG 計画 D8）の基礎資料。
方針：数字は単独実行（他のビルドなし、lake 10 並列）。1 本の時間には環境（import 先の olean）の読み込みを含む。
規約：時間は秒。領域は `SerrePositivity.<A>.<B>` の 2 段まで。
使われ方：重いモジュールを直す順番と、統合でどれだけ減るかの見積もりに使う。再計測は同じ方法で（`lake build SerrePositivity` のログから `Built X (Ns)` を集計）。

## 全体

| 指標 | 値 |
| --- | --- |
| 新規ビルド | 10,660 本 |
| エラボレート時間の合計（CPU） | 19.8 時間（10 並列で実時間 2 時間 09 分） |
| 平均／中央値 | 6.7 秒／5.2 秒 |
| 120 秒超 | 7 本、合計 0.4 時間（全体の 2%） |

**結論 1**：ビルド時間は本数で決まる。中央値 5.2 秒の大半は環境の読み込みなので、統合（DG 1,592 → 126、CategoryTheory 104 → 35、W2a の移動）で本数が減ればそのまま効く。
**結論 2**：巨大な項（例：`KST.SConstruction` の `dgOdotMilnorActualOuterKernelFrameComparison._proof_17`、異なる部分式 1,844・木に展開すると 56 GB）はビルド時間には出ないが、snapshot・監査（`audit_infinity_f1` の RSS 19 GB）・カーネル検査のメモリを食う。別の問題として扱う。

## 領域ごと

| 時間（分） | 本数 | 平均（秒） | 領域 |
| ---: | ---: | ---: | --- |
| 364.2 | 3,378 | 6.5 | InfinityCategories.Derived |
| 253.8 | 1,860 | 8.2 | KST.SConstruction |
| 49.0 | 507 | 5.8 | KST.Spectra |
| 44.1 | 330 | 8.0 | EInfinity.BarrattEccles |
| 41.1 | 258 | 9.6 | KST.DerivedBlowup |
| 39.1 | 295 | 7.9 | EInfinity.Operad |
| 28.8 | 330 | 5.2 | EInfinity.ComplexLimits |
| 26.3 | 277 | 5.7 | KST.LocalizingInvariants |
| 25.0 | 181 | 8.3 | DifferentialGraded.Module |
| 23.1 | 253 | 5.5 | DifferentialGraded.Derived |
| 22.2 | 223 | 6.0 | DifferentialGraded.Tensor |
| 20.5 | 118 | 10.4 | KST.NonConnective |

## 重いモジュール（上位 25）

| 秒 | モジュール |
| ---: | --- |
| 460 | DifferentialGraded.Module.ConeShiftTriangle |
| 286 | EInfinity.BarrattEccles.FreeProbeRelativeUnitWeak |
| 255 | KST.NonConnective.DGKappaResolvedConnectiveMap |
| 185 | InfinityCategories.Derived.Gluing.KernelHomAction |
| 145 | KST.SConstruction.DGOdotMilnorNuNullHom |
| 143 | KST.SConstruction.DGOdotMilnorRightAxisNativeSquare |
| 134 | KST.SConstruction.DGOdotMilnorRightAxisPerfNativeNaturality |
| 119 | KST.DerivedBlowup.FiniteOverlapExceptionalProductComponents |
| 117 | KST.DerivedBlowup.ExceptionalScalarDGFunctor |
| 115 | InfinityCategories.Derived.DGModuleAugmentationRawFactorSquare |
| 113 | InfinityCategories.Derived.CoherentBar.Compact.EvaluationChartLegs |
| 111 | InfinityCategories.Derived.Gluing.MilnorFreeHomTransportComponents |
| 107 | KST.SConstruction.DGIdentityHomGluingRealizedConeInputBoundary |
| 106 | EInfinity.BarrattEccles.FreeProbeRelativeElementForgetFamily |
| 105 | KST.SConstruction.DGKFixedNullPerfectMap |
| 105 | KST.SConstruction.DGIdentityHomGluingInverseRotationRealizedBoundary |
| 104 | KST.SConstruction.DGIdentityHomGluingInverseRotationUpperActualBoundary |
| 100 | KST.SConstruction.DGIdentityHomGluingUpperPerfectVertices |
| 96 | KST.SConstruction.DGOdotTargetCornerRecovery |
| 95 | KST.SConstruction.DGOdotInputMorita |
| 93 | KST.SConstruction.DGKPerfectNuEquivalence |
| 92 | KST.SConstruction.DGPerfectComparisonInverseRotationPerfectBoundary |
| 91 | KST.SConstruction.DGOdotTargetSmallInputMorita |
| 89 | DifferentialGraded.Resolution.Cells.CompositionComparison |
| 87 | EInfinity.Operad.HadamardAssociativity |

## 巨大な項（メモリ）

snapshot の採取（IF-W0-3 §10.19）で、木に展開すると 1 GB を超える項を `scripts/refactor/targets/huge-terms-2026-11.md` に列挙する。監査ごとの RSS（IF-W0-4 の runner）と突き合わせる。
