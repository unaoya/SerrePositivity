# R2-D 監査・集約対応表（2026-10-27、r2d2.py で自動生成）

概要：監査スクリプトの被覆、verify.sh の実行・ビルド範囲、import 専用モジュールの分類、audit_targets の差分を一括で記録する。
方針：集約の判定はコメント除去後の本文で行い、検査専用（#print axioms・assert_no_sorry のみ）と互換入口（export・attribute 等）を集約から分離する。
規約：数値は生成時点の作業木（未追跡の作業葉を含む）。R 窓では再生成して差し替える。

モジュール 33611 本（root 含む、未追跡 13）。宣言を持つ 33013、集約 135、転送入口 179、検査専用 278、互換入口 6。集約＋転送入口のうち同名ディレクトリつき 34 本。
監査スクリプト 98 本（scripts/audit_*.lean 92、scripts/audit/*.lean 5、refactor/audit_sorries 1）。verify.sh が実行するのは 25 本（for 一覧 24 ＋ audit_sorries）。
全監査の閉包 33449 本、未被覆 162 本（うち未追跡 6、追跡済み 156、孤立 137）。root（main_statement）閉包 23472 本、root 閉包かつ未被覆 0 本。
verify.sh がビルドする範囲（root 閉包 ∪ scripts/audit_*.lean の閉包）32455 本。監査閉包にあるが verify.sh でビルドされないもの 994 本（scripts/audit/*.lean のみが import）。

## 1. import 専用モジュールの分類

- 集約：宣言 0、コメント除去後の本文がヘッダ命令だけ、SerrePositivity 配下 import ≥ 2。
- 転送入口：同上で import が 1 本（旧名から新所在への転送）。
- 検査専用：宣言 0、本文が #print axioms・assert_no_sorry・#check 等のみ（Checks 系・Audit 系）。
- 互換入口：宣言 0、export・attribute・alias などを含む。
- 以前の「85 本」（r_survey.py：宣言 0・import ≥3・非 import 行 ≤12）は集約の部分集合。K-B3 の KST 24／12 は、本表の KST 集約＋転送入口（下記）と照合する。

| ディレクトリ | 集約 | 転送入口 | 検査専用 | 互換入口 |
|---|---:|---:|---:|---:|
| DifferentialGraded | 17 | 0 | 277 | 1 |
| HomotopicalAlgebra | 5 | 125 | 0 | 0 |
| PerfectComplex | 31 | 2 | 0 | 0 |
| CategoryTheory | 1 | 25 | 0 | 0 |
| InfinityCategories/Derived | 14 | 1 | 0 | 0 |
| InfinityCategories/F2 | 12 | 0 | 1 | 0 |
| Spectra | 3 | 6 | 0 | 1 |
| KTheory | 6 | 3 | 0 | 0 |
| KST/Spectra | 6 | 0 | 0 | 0 |
| InfinityCategories/F1 | 4 | 2 | 0 | 0 |
| EInfinity | 2 | 3 | 0 | 0 |
| Paper | 1 | 4 | 0 | 0 |
| InfinityCategories/Core | 3 | 2 | 0 | 0 |
| KST/SConstruction | 3 | 0 | 0 | 1 |
| KST/Fibration | 4 | 0 | 0 | 0 |
| BhattScholze | 2 | 0 | 0 | 1 |
| HomologicalAlgebra | 2 | 1 | 0 | 0 |
| KST/LocalizingInvariants | 2 | 0 | 0 | 1 |
| KST/Descent | 2 | 1 | 0 | 0 |
| Inputs | 0 | 3 | 0 | 0 |
| CLMST | 1 | 0 | 0 | 1 |
| (root) | 1 | 0 | 0 | 0 |
| CommutativeAlgebra | 0 | 1 | 0 | 0 |
| LengthAlgebra | 1 | 0 | 0 | 0 |
| KST/NonConnective | 1 | 0 | 0 | 0 |
| KST/ProExcision | 1 | 0 | 0 | 0 |
| KST/SchemeLemmas | 1 | 0 | 0 | 0 |
| KST/DerivedBlowup | 1 | 0 | 0 | 0 |
| KST/DerivedGeometry | 1 | 0 | 0 | 0 |
| KST/Comparison | 1 | 0 | 0 | 0 |
| InfinityCategories/DoldKanComparison | 1 | 0 | 0 | 0 |
| InfinityCategories/Coherent | 1 | 0 | 0 | 0 |
| InfinityCategories/F1B | 1 | 0 | 0 | 0 |
| InfinityCategories/DGNerve | 1 | 0 | 0 | 0 |
| InfinityCategories/Stable | 1 | 0 | 0 | 0 |
| InfinityCategories/HomotopyLimits | 1 | 0 | 0 | 0 |

### 1.1 KST の import 専用モジュール（全件、種別・同名ディレクトリ・直接 import する監査）
- KST.Comparison：aggregate、同名 dir、import 112、監査 audit_kst_comparison.lean
- KST.DerivedBlowup：aggregate、同名 dir、import 342、監査 audit_kst_derived_blowup.lean
- KST.DerivedGeometry：aggregate、同名 dir、import 185、監査 audit_kst_derived_geometry.lean
- KST.Descent：redirect、同名 dir、import 1、監査 audit_kst_descent.lean, audit_kst_descent_main.lean
- KST.Descent.Auxiliary：aggregate、import 251、監査 audit_kst_descent.lean
- KST.Descent.Main：aggregate、import 11、監査 なし（間接被覆）
- KST.Fibration：aggregate、同名 dir、import 750、監査 audit_kst_fibration.lean
- KST.Fibration.Relative.All：aggregate、import 10、監査 audit_kst_fibration.lean
- KST.Fibration.Relative.ClosedStableAll：aggregate、import 15、監査 audit_infinity_core_supply_s1_closed_stable.lean, audit_kst_fibration_relative.lean
- KST.Fibration.Relative.FibrationSupply：aggregate、import 4、監査 なし（間接被覆）
- KST.LocalizingInvariants：compat、同名 dir、import 1889、監査 なし（間接被覆）
- KST.LocalizingInvariants.CoreFlag.All：aggregate、import 9、監査 audit_kst_core_flag.lean
- KST.LocalizingInvariants.CoreFlag.KanPullbackAll：aggregate、import 2、監査 audit_kst_core_flag.lean
- KST.NonConnective：aggregate、同名 dir、import 211、監査 audit_kst_nonconnective.lean
- KST.ProExcision：aggregate、同名 dir、import 360、監査 audit_kst_pro_excision.lean
- KST.SConstruction：compat、同名 dir、import 2842、監査 なし（間接被覆）
- KST.SConstruction.Cofinality：aggregate、同名 dir、import 108、監査 audit_kst_cofinality.lean
- KST.SConstruction.DGKPerfectComposition：aggregate、import 2、監査 なし（間接被覆）
- KST.SConstruction.OdotTailAll：aggregate、import 4、監査 audit_kst_s_construction_tail.lean
- KST.SchemeLemmas：aggregate、同名 dir、import 314、監査 audit_kst_scheme_lemmas.lean
- KST.Spectra：aggregate、同名 dir、import 1010、監査 audit_kst_spectra.lean
- KST.Spectra.D3All：aggregate、import 28、監査 audit_kst_spectra_d3.lean
- KST.Spectra.D3TailAll：aggregate、import 2、監査 audit_kst_spectra_d3tail.lean
- KST.Spectra.FixedPoints：aggregate、import 242、監査 なし（間接被覆）
- KST.Spectra.Rationalization：aggregate、import 56、監査 なし（間接被覆）
- KST.Spectra.S3All：aggregate、import 3、監査 audit_kst_spectra_s3.lean

### 1.2 互換入口の例（先頭 12）
- BhattScholze.Andre.PowerRootEnvelope.Audit.VarpiComparison：assert_no_sorry span_power_eq_of_unit / assert_no_sorry completelyFlat_of_le
- CLMST.Inputs.AlmostLength：alias cyclic_length_eq_zero_of_not_dvd := SerrePositivity.CL / alias cyclic_length_eq_zero := SerrePositivity.CLMST.cyclic_
- DifferentialGraded.Checks.DGCellBoundaryInterchange：#print axioms SerrePositivity.DifferentialGraded.DGCellAttac / #print axioms SerrePositivity.DifferentialGraded.DGCellAttac
- KST.LocalizingInvariants：SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovS / SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovS
- KST.SConstruction：SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssem / SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssem
- Spectra.ModelCategory.SimplicialGenerators：alias boundaryGenerator_domain_presentable := / SerrePositivity.SimplicialModel.boundaryGenerator_domain_pre

## 2. 監査スクリプト一覧（閉包の大きい順）

| 監査 | verify 実行 | 直接 import | 閉包 | #print axioms | assert_no_sorry | 直接 import 先（集約は *、先頭 3） |
|---|:-:|---:|---:|---:|---:|---|
| audit_axioms.lean |  | 1 | 23472 | 54 | 49 | *(root) |
| refactor/audit_sorries.lean | ○ | 1 | 23472 | 0 | 0 | *(root) |
| audit_localizing_invariants.lean | ○ | 2 | 13947 | 0 | 0 | InfinityCategories.Core.LimitProjectionExistence, KST.LocalizingInvariants |
| audit_kst_nonconnective.lean | ○ | 1 | 12821 | 0 | 0 | *KST.NonConnective |
| audit_kst_s_construction.lean | ○ | 3 | 12051 | 14132 | 0 | KST.SConstruction, KST.SConstruction.DGKPerfectCompositionGeneral, KST.SConstruction.PresentedPerfectDGNativeLabel |
| audit_kst_fibration.lean | ○ | 2 | 11595 | 0 | 0 | *KST.Fibration, *KST.Fibration.Relative.All |
| audit_derived_infinity.lean | ○ | 1989 | 11287 | 2313 | 0 | DifferentialGraded.Morita.PerfectProjectiveImage, InfinityCategories.Derived.CoherentBar.Compact.ConeDerivedEquivalence, InfinityCategories.Derived.KappaPerfect.SphereClosureCompactComparison … |
| audit_kst_s_construction_tail.lean |  | 1 | 9926 | 40 | 0 | *KST.SConstruction.OdotTailAll |
| audit_kst_spectra_s3.lean |  | 1 | 9715 | 0 | 0 | *KST.Spectra.S3All |
| audit_derived_gluing.lean | ○ | 1 | 9608 | 0 | 0 | *InfinityCategories.Derived.Gluing |
| audit_derived_native_family.lean |  | 12 | 9223 | 0 | 0 | InfinityCategories.Derived.CoherentBar.Compact.ConeDerivedEquivalence, InfinityCategories.Derived.KappaPerfect.SphereClosureCompactComparison, InfinityCategories.Derived.CoherentBar.Compact.SuspensionFixedCoherenceTypes … |
| audit_derived_closure_functoriality.lean |  | 2 | 9220 | 0 | 0 | *InfinityCategories.Derived.ClosureFunctoriality.All, *InfinityCategories.Derived.SuspensionAction.All |
| audit_einfinity.lean | ○ | 1 | 8687 | 0 | 0 | *EInfinity |
| audit_infinity_stable.lean | ○ | 2106 | 8571 | 2754 | 0 | *InfinityCategories.Derived.CoherentBar.Compact.All, InfinityCategories.Stable.RetractComplementCofiber, InfinityCategories.Stable.IdempotentCompletionDensity … |
| audit_derived_native_p.lean |  | 1 | 7960 | 0 | 0 | InfinityCategories.Derived.DGSuspensionNativeNaturalityModel |
| audit_derived_suspension_coherent.lean |  | 1 | 7496 | 0 | 0 | InfinityCategories.Derived.DGSuspensionCoherentSquareInput |
| audit_derived_suspension_native.lean |  | 1 | 7494 | 1 | 0 | InfinityCategories.Derived.DGSuspensionNativeSquareModel |
| audit_derived_suspension_replacement.lean |  | 1 | 7494 | 0 | 0 | InfinityCategories.Derived.DGSuspensionNativeSquareReplacement |
| audit_dg_cell_comparison.lean |  | 1 | 7302 | 1 | 0 | InfinityCategories.Derived.DGKappaSuspensionCanonicalMapData |
| audit_homotopy_limits.lean | ○ | 2 | 6976 | 5553 | 0 | *InfinityCategories.F2.Presentable, *InfinityCategories.HomotopyLimits |
| audit_infinity_f2.lean | ○ | 8 | 6775 | 0 | 0 | InfinityCategories.F2, InfinityCategories.F2.Ind.PullbacksArePushouts, InfinityCategories.F2.Ind.YonedaExactFunctor … |
| audit_derived_sphere_closure.lean |  | 2 | 6646 | 0 | 0 | InfinityCategories.Derived.KappaPerfect.SphereClosureInput, InfinityCategories.Derived.DGKappaSphereClosureSemifreeCovers |
| audit_derived_coherent_bar_compact.lean |  | 1 | 6636 | 1 | 0 | *InfinityCategories.Derived.CoherentBar.Compact.All |
| audit_infinity_presentable.lean | ○ | 1 | 6402 | 1 | 0 | *InfinityCategories.F2.Presentable |
| audit_derived_coherent_bar_strict.lean |  | 1 | 6192 | 0 | 0 | *InfinityCategories.Derived.CoherentBar.StrictComparison.All |
| audit_infinity_presentable_localization.lean |  | 1 | 5907 | 7 | 0 | *InfinityCategories.F2.Presentable.Localization.All |
| audit_infinity_presentable_local_objects.lean |  | 1 | 5891 | 0 | 0 | *InfinityCategories.F2.Presentable.Localization.LocalObjects.All |
| audit_derived_kappa_perfect.lean |  | 2 | 5712 | 0 | 0 | *InfinityCategories.Derived.KappaPerfect.All, *InfinityCategories.Derived.KappaCovers.All |
| audit_infinity_accessible_pullback.lean |  | 1 | 5346 | 0 | 0 | *InfinityCategories.F2.Presentable.AccessiblePullback.All |
| audit_kst_cofinality.lean |  | 1 | 5292 | 1 | 0 | *KST.SConstruction.Cofinality |
| audit_kst_core_flag.lean |  | 2 | 5143 | 37 | 0 | *KST.LocalizingInvariants.CoreFlag.All, *KST.LocalizingInvariants.CoreFlag.KanPullbackAll |
| audit_kst_spectra_d3tail.lean |  | 1 | 5143 | 0 | 0 | *KST.Spectra.D3TailAll |
| audit_infinity_presentable_supply.lean |  | 2 | 5060 | 0 | 0 | *InfinityCategories.F2.Presentable.Supply.All, InfinityCategories.F2.Presentable.CosliceBaseChangePreservation |
| audit_infinity_presentable_duality.lean |  | 1 | 4974 | 0 | 0 | *InfinityCategories.F2.Presentable.Duality.All |
| audit_f2_ind.lean | ○ | 11 | 4851 | 546 | 0 | *InfinityCategories.F2.Ind, InfinityCategories.F2.Ind.FiniteColimitCoconeFamily, InfinityCategories.F2.Ind.FiniteLimitConeFamily … |
| audit_infinity_f1_f1b.lean | ○ | 3 | 4683 | 0 | 0 | *InfinityCategories.F1.Cocartesian, *InfinityCategories.F1, *InfinityCategories.F1B |
| audit_infinity_f1.lean | ○ | 11 | 4215 | 38 | 0 | *InfinityCategories.F1.Cocartesian, *InfinityCategories.F1, InfinityCategories.F1.Yoneda.YonedaLimits … |
| audit_kst_spectra_d3.lean |  | 1 | 4122 | 0 | 0 | *KST.Spectra.D3All |
| audit_f2_compact.lean | ○ | 1 | 4110 | 280 | 0 | *InfinityCategories.F2.Compact |
| audit_infinity_f2_exchange.lean |  | 39 | 3771 | 0 | 0 | InfinityCategories.F2.FilteredExchange.CompositionConePostFace, InfinityCategories.F2.FilteredExchange.PointedRightFamilyFixedEvaluation, InfinityCategories.F2.FilteredExchange.PointedValueFamilyTwoStage … |
| audit_infinity_core_supply_s1_closed_stable.lean |  | 1 | 3460 | 0 | 0 | *KST.Fibration.Relative.ClosedStableAll |
| audit_kst_fibration_relative.lean |  | 1 | 3460 | 0 | 0 | *KST.Fibration.Relative.ClosedStableAll |
| audit_kst_spectra.lean | ○ | 1 | 3228 | 0 | 0 | *KST.Spectra |
| audit_f2_idempotent.lean | ○ | 1 | 3148 | 609 | 0 | *InfinityCategories.F2.Idempotent |
| audit_f2_pi_criterion.lean |  | 1 | 2985 | 1 | 0 | *InfinityCategories.F2.FilteredExchange.PiCriterion.All |
| audit/shared.lean |  | 1621 | 2775 | 0 | 0 | Asymptotic.AssembleComplex, Asymptotic.BaseChangeComparison, Asymptotic.BaseChangeComposition … |
| audit/dg.lean |  | 2144 | 2309 | 0 | 0 | DifferentialGraded.Bimodule.Action, DifferentialGraded.Bimodule.ActionElement, DifferentialGraded.Bimodule.ActionEvaluation … |
| audit_derived_coherent_bar.lean |  | 1 | 1752 | 0 | 0 | *InfinityCategories.Derived.CoherentBar.All |
| audit_infinity_f1b.lean | ○ | 6 | 1484 | 28 | 0 | *InfinityCategories.F1B, InfinityCategories.F1B.Localization.UniversalConsequences, InfinityCategories.F1B.Localization.UniverseDescent … |
| audit_clmst.lean |  | 106 | 1480 | 22 | 1067 | CommutativeAlgebra.GenericEtale, CommutativeAlgebra.RootTower.CompletedFrobenius, CommutativeAlgebra.WittAdditionCarry … |
| audit/clmst.lean |  | 146 | 1465 | 0 | 0 | CLMST.Algebra, CLMST.AllModuleAlmostTor, CLMST.AllModuleTorFromBS … |
| audit_dg_quotient_parameter.lean |  | 7 | 1358 | 1 | 0 | InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonNativeComposition, InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonFamilyLift, InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonNative … |
| audit_derived_cell_projective.lean |  | 1 | 1338 | 1 | 0 | InfinityCategories.Derived.DGGluingCellProjectiveInput |
| audit_kst_derived_blowup.lean |  | 1 | 1289 | 0 | 0 | *KST.DerivedBlowup |
| audit_kst_descent.lean |  | 2 | 1244 | 0 | 0 | *KST.Descent, *KST.Descent.Auxiliary |
| audit_clmst_b3.lean |  | 10 | 1057 | 0 | 84 | CommutativeAlgebra.PerfectoidizationFunctor, BhattScholze.Semiperfectoid.Perfectoidization, CommutativeAlgebra.PerfectoidIdeal … |
| audit_homotopical_rectification.lean |  | 1 | 1049 | 0 | 0 | *HomotopicalAlgebra.Rectification.Foundations |
| audit_kst_derived_geometry.lean |  | 1 | 1040 | 0 | 0 | *KST.DerivedGeometry |
| audit/bhatt_scholze.lean |  | 124 | 1016 | 0 | 0 | BhattScholze.Andre.Variants.ArbitraryFamily, BhattScholze.Andre.Variants.RootedExtension, BhattScholze.Prism.Bounded.Completeness … |
| audit_f7.lean |  | 2 | 1008 | 0 | 3 | CommutativeAlgebra.PerfectoidFontaineSeparation, *BhattScholze |
| audit_f5.lean |  | 2 | 1005 | 0 | 4 | CommutativeAlgebra.AdicBoundedTorsionQuotient, *BhattScholze |
| audit_kst_descent_main.lean |  | 1 | 963 | 0 | 0 | *KST.Descent |
| audit_bhatt_scholze_b5.lean |  | 4 | 943 | 31 | 31 | BhattScholze.Almost.PerfectoidAlmost, BhattScholze.Almost.Lemma103, HomologicalAlgebra.DerivedCompletion.CompletedTensorShortExact … |
| audit_bhatt_scholze_prop813.lean |  | 2 | 940 | 32 | 32 | BhattScholze.Perfectoidization.CompletedTensor, BhattScholze.Perfectoidization.TensorCompatibility |
| audit_kst_comparison.lean |  | 1 | 863 | 1500 | 0 | *KST.Comparison |
| audit_kst_pro_excision.lean |  | 1 | 783 | 1644 | 0 | *KST.ProExcision |
| audit_bhatt_scholze_arc_excision.lean |  | 2 | 728 | 3 | 1 | BhattScholze.Perfectoidization.Derived.Excision, BhattScholze.Perfectoidization.Excision |
| audit_stage4_contract.lean |  | 83 | 663 | 0 | 0 | HomotopicalAlgebra.HomotopyFunctionComplex.ChosenComparison, HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison, HomotopicalAlgebra.HomotopyFunctionComplex.PiZero … |
| audit_refactor_infinity.lean | ○ | 33 | 638 | 0 | 0 | *InfinityCategories.Core, InfinityCategories.Core.LeftFiberKan, InfinityCategories.Core.PrismVerticalSimplex … |
| audit_homotopical_foundations.lean |  | 1 | 624 | 0 | 0 | *HomotopicalAlgebra.Foundations |
| audit_dg_perfect_projective_image.lean |  | 1 | 551 | 3 | 0 | DifferentialGraded.Morita.PerfectProjectiveImage |
| audit/adams.lean |  | 172 | 545 | 0 | 0 | IntersectionMultiplicity.AdamsVanishing, IntersectionMultiplicity.AdamsVanishingAll, IntersectionMultiplicity.AdamsVanishingThree … |
| audit_dold_kan_comparison.lean | ○ | 1 | 516 | 645 | 0 | *InfinityCategories.DoldKanComparison |
| audit_andre_unoriented.lean |  | 1 | 429 | 0 | 19 | BhattScholze.Andre.PowerRootEnvelope.Initiality |
| audit_bhatt_scholze_b4.lean |  | 48 | 420 | 2369 | 2369 | BhattScholze.Semiperfectoid.Surjectivity, BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrism, BhattScholze.Prism.Residue.PrismaticResidue … |
| audit_bhatt_scholze_refactoring.lean |  | 30 | 418 | 137 | 190 | BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrism, BhattScholze.Andre.Perfection.DeltaAlgebra, BhattScholze.Semiperfectoid.CompatibleRootPerfectoid … |
| audit_andre_initial_coefficient.lean |  | 1 | 416 | 2 | 20 | BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue |
| audit_bhatt_scholze_andre_conditional.lean |  | 1 | 415 | 2 | 2 | BhattScholze.Semiperfectoid.Surjectivity |
| audit_kst_scheme_lemmas.lean |  | 1 | 369 | 0 | 0 | *KST.SchemeLemmas |
| audit_homotopical_general_tools.lean |  | 1 | 355 | 0 | 0 | *HomotopicalAlgebra.GeneralTools |
| audit_spectra.lean | ○ | 16 | 349 | 0 | 0 | *Spectra.Foundations, CategoryTheory.Monoidal.RepresentedHomFunctor, CategoryTheory.Monoidal.MappingParametrizedAdjunction … |
| audit_infinity_core.lean | ○ | 2 | 345 | 1593 | 0 | *InfinityCategories.Core, InfinityCategories.Core.UniverseEdgeTransport |
| audit_dg_nerve.lean | ○ | 2 | 334 | 1086 | 0 | InfinityCategories.Derived.SemifreeLimits, *InfinityCategories.DGNerve |
| audit_derived_coherent_bar_retract.lean |  | 1 | 308 | 0 | 0 | *InfinityCategories.Derived.CoherentBar.Retract.All |
| audit_general_spectra.lean |  | 2 | 250 | 0 | 0 | *Spectra.General.Foundations, Spectra.General.SimplicialComparison |
| audit_local_algebra.lean |  | 142 | 203 | 866 | 866 | LinearAlgebra.IndependentPerturbation, CommutativeAlgebra.DerivationIdealSpan, FieldTheory.PMonomial … |
| audit_bhatt_scholze.lean |  | 25 | 159 | 574 | 577 | BhattScholze.Semiperfectoid.Perfectoidization, BhattScholze.Prism.PerfectPrismHomLift, BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid … |
| audit_infinity_core_supply_s1_triangle.lean |  | 1 | 138 | 0 | 0 | *InfinityCategories.F1.Diagrams.NativeTriangleSupplyAll |
| audit_euler_group_shared.lean |  | 3 | 122 | 4 | 11 | CategoryTheory.HomologicalEuler, KTheory.HomologyEuler, PerfectComplex.OrdinaryEuler |
| audit_triangulated_k0_shift_shared.lean |  | 2 | 105 | 2 | 2 | CategoryTheory.TriangulatedK0Shift, KTheory.ResolutionClass |
| audit_euler_betti_finite_support.lean |  | 2 | 86 | 1 | 3 | CategoryTheory.HomologicalEuler, Asymptotic.CompletedRankEvaluation |
| audit_coherent_nerve.lean | ○ | 1 | 41 | 234 | 0 | *InfinityCategories.Coherent |
| audit_homotopy_cone_representative_shared.lean |  | 4 | 40 | 3 | 6 | PerfectComplex.ClosedSupportRelations, PerfectComplex.K0Comparison, CategoryTheory.BoundedHomotopy … |
| audit_exact_euler_finite_support.lean |  | 2 | 16 | 1 | 4 | CategoryTheory.HomologicalEuler, LengthAlgebra.ExactSequenceEuler |
| audit_adams_action_transport.lean |  | 3 | 6 | 2 | 4 | PerfectComplex.CubicActionTransport, CategoryTheory.ShortExactCokernel, CategoryTheory.ThreeComponentMaps |
| audit_f6.lean |  | 2 | 5 | 0 | 7 | CommutativeAlgebra.PerfectionPrincipalQuotientKernel, CommutativeAlgebra.PerfectionPrincipalKernel |
| audit_f4.lean |  | 1 | 3 | 0 | 5 | CommutativeAlgebra.StrictPRecovery |
| audit_homotopy_property_shared.lean |  | 1 | 2 | 1 | 1 | CategoryTheory.HomotopyProperty |

## 3. verify.sh が実行しない監査

73 本。公理・sorry 検査を持つ（#print axioms または assert_no_sorry ≥1）37 本、ビルド専用（検査 0）36 本。「ビルド包含」は直接 import が実行一覧の閉包に入ること（46 本）。

### 3.1 検査を持つのに実行されない監査（優先追加候補）
- audit_bhatt_scholze_b4.lean：検査 4738、閉包 420
- audit_local_algebra.lean：検査 1732、閉包 203、ビルド包含
- audit_kst_pro_excision.lean：検査 1644、閉包 783、ビルド包含
- audit_kst_comparison.lean：検査 1500、閉包 863、ビルド包含
- audit_bhatt_scholze.lean：検査 1151、閉包 159
- audit_clmst.lean：検査 1089、閉包 1480
- audit_bhatt_scholze_refactoring.lean：検査 327、閉包 418
- audit_axioms.lean：検査 103、閉包 23472、ビルド包含
- audit_clmst_b3.lean：検査 84、閉包 1057、ビルド包含
- audit_bhatt_scholze_prop813.lean：検査 64、閉包 940
- audit_bhatt_scholze_b5.lean：検査 62、閉包 943、ビルド包含
- audit_kst_s_construction_tail.lean：検査 40、閉包 9926
- audit_kst_core_flag.lean：検査 37、閉包 5143、ビルド包含
- audit_andre_initial_coefficient.lean：検査 22、閉包 416、ビルド包含
- audit_andre_unoriented.lean：検査 19、閉包 429、ビルド包含
- audit_euler_group_shared.lean：検査 15、閉包 122、ビルド包含
- audit_homotopy_cone_representative_shared.lean：検査 9、閉包 40、ビルド包含
- audit_f6.lean：検査 7、閉包 5、ビルド包含
- audit_infinity_presentable_localization.lean：検査 7、閉包 5907、ビルド包含
- audit_adams_action_transport.lean：検査 6、閉包 6、ビルド包含
- audit_exact_euler_finite_support.lean：検査 5、閉包 16、ビルド包含
- audit_f4.lean：検査 5、閉包 3、ビルド包含
- audit_bhatt_scholze_andre_conditional.lean：検査 4、閉包 415、ビルド包含
- audit_bhatt_scholze_arc_excision.lean：検査 4、閉包 728、ビルド包含
- audit_euler_betti_finite_support.lean：検査 4、閉包 86、ビルド包含
- audit_f5.lean：検査 4、閉包 1005、ビルド包含
- audit_triangulated_k0_shift_shared.lean：検査 4、閉包 105、ビルド包含
- audit_dg_perfect_projective_image.lean：検査 3、閉包 551、ビルド包含
- audit_f7.lean：検査 3、閉包 1008、ビルド包含
- audit_homotopy_property_shared.lean：検査 2、閉包 2、ビルド包含
- audit_derived_cell_projective.lean：検査 1、閉包 1338、ビルド包含
- audit_derived_coherent_bar_compact.lean：検査 1、閉包 6636、ビルド包含
- audit_derived_suspension_native.lean：検査 1、閉包 7494、ビルド包含
- audit_dg_cell_comparison.lean：検査 1、閉包 7302、ビルド包含
- audit_dg_quotient_parameter.lean：検査 1、閉包 1358、ビルド包含
- audit_f2_pi_criterion.lean：検査 1、閉包 2985
- audit_kst_cofinality.lean：検査 1、閉包 5292

### 3.2 ビルド専用で実行されない監査
- audit_kst_spectra_s3.lean：閉包 9715
- audit_derived_native_family.lean：閉包 9223、ビルド包含
- audit_derived_closure_functoriality.lean：閉包 9220
- audit_derived_native_p.lean：閉包 7960、ビルド包含
- audit_derived_suspension_coherent.lean：閉包 7496、ビルド包含
- audit_derived_suspension_replacement.lean：閉包 7494、ビルド包含
- audit_derived_sphere_closure.lean：閉包 6646、ビルド包含
- audit_derived_coherent_bar_strict.lean：閉包 6192
- audit_infinity_presentable_local_objects.lean：閉包 5891、ビルド包含
- audit_derived_kappa_perfect.lean：閉包 5712
- audit_infinity_accessible_pullback.lean：閉包 5346、ビルド包含
- audit_kst_spectra_d3tail.lean：閉包 5143
- audit_infinity_presentable_supply.lean：閉包 5060、ビルド包含
- audit_infinity_presentable_duality.lean：閉包 4974、ビルド包含
- audit_kst_spectra_d3.lean：閉包 4122
- audit_infinity_f2_exchange.lean：閉包 3771
- audit_infinity_core_supply_s1_closed_stable.lean：閉包 3460、ビルド包含
- audit_kst_fibration_relative.lean：閉包 3460、ビルド包含
- audit/shared.lean：閉包 2775
- audit/dg.lean：閉包 2309
- audit_derived_coherent_bar.lean：閉包 1752
- audit/clmst.lean：閉包 1465
- audit_kst_derived_blowup.lean：閉包 1289、ビルド包含
- audit_kst_descent.lean：閉包 1244
- audit_homotopical_rectification.lean：閉包 1049
- audit_kst_derived_geometry.lean：閉包 1040、ビルド包含
- audit/bhatt_scholze.lean：閉包 1016
- audit_kst_descent_main.lean：閉包 963、ビルド包含
- audit_stage4_contract.lean：閉包 663
- audit_homotopical_foundations.lean：閉包 624
- audit/adams.lean：閉包 545
- audit_kst_scheme_lemmas.lean：閉包 369、ビルド包含
- audit_homotopical_general_tools.lean：閉包 355
- audit_derived_coherent_bar_retract.lean：閉包 308
- audit_general_spectra.lean：閉包 250、ビルド包含
- audit_infinity_core_supply_s1_triangle.lean：閉包 138、ビルド包含

## 4. 集約と監査の対応

集約＋転送入口 314 本：監査が直接 import する 157、間接被覆 33、未被覆 124。

### 4.1 未被覆の集約・転送入口（全件）
- HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.BarSize（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleBinary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleHorn（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.DegenerateHornInput（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.DegenerateHornOverlap（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.FreeWordHom（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.KanComparisonSquare（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.KanComparisonTetrahedron（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.KanComparisonTriangle（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.KanHornFamilyLifting（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.KanTriangleFamily（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.LargeParameterSquare（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NaturalHornFilling（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveArrowComparison（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBinaryBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameter（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterComposition（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterMaps（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBoundaryExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCoherentExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCoherentFamily（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCoherentReindex（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCylinderBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCylinderExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveDiagramExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveEvaluationLaws（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveFillerExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveFirstChoice（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveInitialImage（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveIntervalBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveLargeParameter（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveLargeSampling（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveLowerExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingParameter（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveNaturalBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveParameterExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NervePrescribedCells（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveProductParameter（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NervePushoutBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NerveSmallFamilies（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornFilling（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornInputMap（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetFaces（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.ParameterizedHornChoices（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RecursiveChoiceExtension（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeBoundaryFilling（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceCells（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceFunctor（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceIso（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceMaps（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceSpace（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeComparisonTriangle（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeHornFillingOperation（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RestrictionDescentChoices（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RetractChainFamily（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.RetractChainUnits（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SegmentWords（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SelectedLoopContraction（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SelectedTriangle（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SmallDiagramQuotient（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SmallKanHomotopy（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SmallParameterClosure（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.StrictValueDescentCounterexample（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.StrictValueObstruction（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.StrictValuePresentationCounterexample（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.TriangleDegeneracyParameters（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WeightedWordHom（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationAction（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationAugmentation（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationCat（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationDiagram（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationNaturality（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationRealization（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationSection（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationSourceMap（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordRetractChainFamily（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordRetractionAction（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordSegment（redirect、import 1、被 import 0）
- HomotopicalAlgebra.Simplicial.WordSegmentComparison（redirect、import 1、被 import 0）
- Spectra.SymmetricSequence.AdjacentTranspositions（redirect、import 1、被 import 0）
- Spectra.SymmetricSequence.TensorPermutations（redirect、import 1、被 import 0）
- Spectra.SymmetricSequence.TensorPowers（redirect、import 1、被 import 0）

### 4.2 間接被覆の集約・転送入口（全件）
- EInfinity.BarrattEccles（aggregate、import 123）
- EInfinity.ComplexLimits.ExtendTruncationHom（redirect、import 1）
- EInfinity.ComplexLimits.ExtendTruncationHomNaturality（redirect、import 1）
- EInfinity.ComplexLimits.TruncationInclusionNaturality（redirect、import 1）
- HomotopicalAlgebra.Rectification.CategoryTheory.LabelledChain（redirect、import 1）
- HomotopicalAlgebra.Rectification.CategoryTheory.SimplexChainParameter（redirect、import 1）
- HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FreePathResolution（redirect、import 1）
- HomotopicalAlgebra.Rectification.Simplicial.NerveInitialImage（aggregate、import 3）
- HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace（aggregate、import 3）
- HomotopicalAlgebra.Rectification.Simplicial.SmallParameterClosure（redirect、import 1）
- InfinityCategories.Core.Fibrations（aggregate、import 4）
- InfinityCategories.Core.InvertibleEdge（redirect、import 1）
- InfinityCategories.Core.MappingSpace（aggregate、import 9）
- InfinityCategories.Core.MappingSpaceKan（redirect、import 1）
- InfinityCategories.Derived.DGClosedSlicePrismNaturality（aggregate、import 4）
- InfinityCategories.Derived.DGWalkingHomPrismNaturality（aggregate、import 7）
- InfinityCategories.Derived.Perfect（aggregate、import 5）
- InfinityCategories.Derived.Support（aggregate、import 12）
- InfinityCategories.Derived.SuspensionAction.NativeAll（aggregate、import 3）
- InfinityCategories.F1.Cocartesian.BaseChangeSecondHomDecompositionEndpoints（aggregate、import 2）
- InfinityCategories.F1.Fibrations（aggregate、import 18）
- InfinityCategories.F1.Yoneda.PresheafDensity（redirect、import 1）
- InfinityCategories.F2.CatInfinity（aggregate、import 30）
- InfinityCategories.F2.FilteredExchange（aggregate、import 1113）
- KST.Descent.Main（aggregate、import 11）
- KST.Fibration.Relative.FibrationSupply（aggregate、import 4）
- KST.SConstruction.DGKPerfectComposition（aggregate、import 2）
- KST.Spectra.FixedPoints（aggregate、import 242）
- KST.Spectra.Rationalization（aggregate、import 56）
- Spectra.StageTwo（aggregate、import 3）
- Spectra.SymmetricSequence.AdjacentBraid（redirect、import 1）
- Spectra.SymmetricSequence.DisjointUnion（redirect、import 1）
- Spectra.SymmetricSequence.FiniteBijection（redirect、import 1）

## 5. 未被覆モジュール

| ディレクトリ | 未被覆 | 孤立 | 未追跡 |
|---|---:|---:|---:|
| HomotopicalAlgebra | 122 | 122 | 1 |
| InfinityCategories/F1 | 16 | 4 | 0 |
| InfinityCategories/Derived | 11 | 4 | 0 |
| DifferentialGraded | 6 | 3 | 1 |
| KST/Spectra | 4 | 1 | 4 |
| Spectra | 3 | 3 | 0 |

HomotopicalAlgebra：全 1112 本、root 閉包内 281、監査閉包内 990。

### 5.1 追跡済みの未被覆モジュール（全件）
- DifferentialGraded.Functor.ClosedConjugationPasting（被 import 1）
- DifferentialGraded.Functor.ClosedConjugationTensorComposition（被 import 1）
- DifferentialGraded.Functor.ModuleExtensionConjugation（被 import 1）
- DifferentialGraded.Functor.Small（被 import 0）
- DifferentialGraded.Module.MaurerCartanTargetHomDifferential（被 import 0）
- HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest（被 import 0）
- HomotopicalAlgebra.Simplicial.BarSize（被 import 0）
- HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleBinary（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleHorn（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram（被 import 0）
- HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport（被 import 0）
- HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation（被 import 0）
- HomotopicalAlgebra.Simplicial.DegenerateHornInput（被 import 0）
- HomotopicalAlgebra.Simplicial.DegenerateHornOverlap（被 import 0）
- HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap（被 import 0）
- HomotopicalAlgebra.Simplicial.FreeWordHom（被 import 0）
- HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison（被 import 0）
- HomotopicalAlgebra.Simplicial.KanComparisonSquare（被 import 0）
- HomotopicalAlgebra.Simplicial.KanComparisonTetrahedron（被 import 0）
- HomotopicalAlgebra.Simplicial.KanComparisonTriangle（被 import 0）
- HomotopicalAlgebra.Simplicial.KanHornFamilyLifting（被 import 0）
- HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution（被 import 0）
- HomotopicalAlgebra.Simplicial.KanTriangleFamily（被 import 0）
- HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice（被 import 0）
- HomotopicalAlgebra.Simplicial.LargeParameterSquare（被 import 0）
- HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice（被 import 0）
- HomotopicalAlgebra.Simplicial.NaturalHornFilling（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveArrowComparison（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBinaryBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameter（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterComposition（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBiparameterMaps（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveBoundaryExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCoherentExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCoherentFamily（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCoherentReindex（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCylinderBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveCylinderExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveDiagramExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveEvaluationLaws（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveFillerExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveFirstChoice（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveInitialImage（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveIntervalBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveLargeParameter（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveLargeSampling（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveLowerExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingParameter（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveNaturalBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveParameterExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NervePrescribedCells（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveProductParameter（被 import 0）
- HomotopicalAlgebra.Simplicial.NervePushoutBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.NerveSmallFamilies（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornFilling（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornInputMap（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetFaces（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity（被 import 0）
- HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn（被 import 0）
- HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram（被 import 0）
- HomotopicalAlgebra.Simplicial.ParameterizedHornChoices（被 import 0）
- HomotopicalAlgebra.Simplicial.RecursiveChoiceExtension（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeBoundaryFilling（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceCells（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceFunctor（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceIso（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceMaps（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeChoiceSpace（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeComparisonTriangle（被 import 0）
- HomotopicalAlgebra.Simplicial.RelativeHornFillingOperation（被 import 0）
- HomotopicalAlgebra.Simplicial.RestrictionDescentChoices（被 import 0）
- HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation（被 import 0）
- HomotopicalAlgebra.Simplicial.RetractChainFamily（被 import 0）
- HomotopicalAlgebra.Simplicial.RetractChainUnits（被 import 0）
- HomotopicalAlgebra.Simplicial.SegmentWords（被 import 0）
- HomotopicalAlgebra.Simplicial.SelectedLoopContraction（被 import 0）
- HomotopicalAlgebra.Simplicial.SelectedTriangle（被 import 0）
- HomotopicalAlgebra.Simplicial.SmallDiagramQuotient（被 import 0）
- HomotopicalAlgebra.Simplicial.SmallKanHomotopy（被 import 0）
- HomotopicalAlgebra.Simplicial.SmallParameterClosure（被 import 0）
- HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction（被 import 0）
- HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient（被 import 0）
- HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient（被 import 0）
- HomotopicalAlgebra.Simplicial.StrictValueDescentCounterexample（被 import 0）
- HomotopicalAlgebra.Simplicial.StrictValueObstruction（被 import 0）
- HomotopicalAlgebra.Simplicial.StrictValuePresentationCounterexample（被 import 0）
- HomotopicalAlgebra.Simplicial.TriangleDegeneracyParameters（被 import 0）
- HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy（被 import 0）
- HomotopicalAlgebra.Simplicial.WeightedWordHom（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationAction（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationAugmentation（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationCat（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationDiagram（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationNaturality（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationRealization（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationSection（被 import 0）
- HomotopicalAlgebra.Simplicial.WordPresentationSourceMap（被 import 0）
- HomotopicalAlgebra.Simplicial.WordRetractChainFamily（被 import 0）
- HomotopicalAlgebra.Simplicial.WordRetractionAction（被 import 0）
- HomotopicalAlgebra.Simplicial.WordSegment（被 import 0）
- HomotopicalAlgebra.Simplicial.WordSegmentComparison（被 import 0）
- InfinityCategories.Derived.DGKappaPresentedFreeNativeFunctor（被 import 0）
- InfinityCategories.Derived.DGKappaPresentedSourceAction（被 import 3）
- InfinityCategories.Derived.DGKappaPresentedSourceComposition（被 import 1）
- InfinityCategories.Derived.DGKappaPresentedSourceCompositionIso（被 import 1）
- InfinityCategories.Derived.DGKappaPresentedSourceFunctor（被 import 1）
- InfinityCategories.Derived.DGKappaPresentedSourceInputHomLaws（被 import 1）
- InfinityCategories.Derived.DGKappaPresentedSourceNativeAction（被 import 0）
- InfinityCategories.Derived.DGKappaPresentedSourceNativeFunctor（被 import 0）
- InfinityCategories.Derived.DGKappaPresentedSourceParameter（被 import 1）
- InfinityCategories.Derived.DGKappaPresentedSourceShiftAction（被 import 0）
- InfinityCategories.Derived.DGKappaPresentedSourceUnit（被 import 1）
- InfinityCategories.F1.Diagrams.CanonicalIntervalTriangle（被 import 1）
- InfinityCategories.F1.Diagrams.ContractiblePrescribedRetraction（被 import 1）
- InfinityCategories.F1.Diagrams.ControlledCompositionDiagonalTransport（被 import 0）
- InfinityCategories.F1.Diagrams.ControlledTriangleEncoderParameterEquality（被 import 1）
- InfinityCategories.F1.Diagrams.ControlledTriangleIntervalFaithfulness（被 import 1）
- InfinityCategories.F1.Diagrams.ControlledTriangleNormalizedRequest（被 import 0）
- InfinityCategories.F1.Diagrams.ControlledTrianglePointParameterMono（被 import 0）
- InfinityCategories.F1.Diagrams.ControlledTriangleSplitReduction（被 import 2）
- InfinityCategories.F1.Diagrams.FamilyParameterEquality（被 import 1）
- InfinityCategories.F1.Diagrams.TriangleLabelCoordinateSection（被 import 1）
- InfinityCategories.F1.Diagrams.TrianglePrismCoordinateSection（被 import 1）
- InfinityCategories.F1.Diagrams.TrianglePrismLiftedSection（被 import 1）
- InfinityCategories.F1.Diagrams.TriangleSeparatedLongFaithfulness（被 import 1）
- InfinityCategories.F1.Diagrams.TriangleSeparatedPrismRecovery（被 import 1）
- InfinityCategories.F1.Diagrams.TriangleSeparatedVertexParameter（被 import 1）
- InfinityCategories.F1.Diagrams.WholeDiagonalImageObstruction（被 import 0）
- Spectra.SymmetricSequence.AdjacentTranspositions（被 import 0）
- Spectra.SymmetricSequence.TensorPermutations（被 import 0）
- Spectra.SymmetricSequence.TensorPowers（被 import 0）

### 5.2 未追跡の未被覆モジュール（作業中の葉、全件）
- DifferentialGraded.Morita.ScalarExtensionKernelOutputComponents
- HomotopicalAlgebra.Simplicial.RelativeFillerComparison
- KST.Spectra.PointedParametricUncurryAction
- KST.Spectra.PointedParametricUncurryPre
- KST.Spectra.PointedUncurryActionTensor
- KST.Spectra.PointedUncurryComposition

## 6. audit_targets.txt の差分とビルド漏れ

現行 2822 本、再生成 2744 本（verify.sh と同じ scripts/audit_*.lean から）：追加 52、削除 130。ファイルは verify.sh 実行時に再生成される派生物で、差分は前回実行以降の監査 import の変化を示す。
ビルド漏れ：scripts/audit/*.lean の閉包にあり、root 閉包にも scripts/audit_*.lean の閉包にも入らないモジュール 994 本（ディレクトリ別下記）。

| ディレクトリ | ビルド漏れ |
|---|---:|
| DifferentialGraded | 957 |
| CategoryTheory | 25 |
| BhattScholze | 4 |
| KTheory | 4 |
| Inputs | 3 |
| CommutativeAlgebra | 1 |

### 6.1 追加（監査にあるが現行一覧に無い）
- BhattScholze.Delta.DividedPower.Factorial
- BhattScholze.Delta.DividedPower.PDivision
- BhattScholze.Delta.DividedPower.PDivisionCompletion
- BhattScholze.Delta.DividedPower.PrincipalDP
- BhattScholze.Delta.DividedPower.RankOneDP
- BhattScholze.Delta.Division.Basic
- BhattScholze.Delta.Division.Family
- BhattScholze.Delta.Division.Relations
- BhattScholze.Delta.Division.Residue
- BhattScholze.Delta.Division.Source
- BhattScholze.Delta.Division.Witt
- DifferentialGraded.Morita.PerfectProjectiveImage
- DifferentialGraded.Quotient.FunctorLaws
- DifferentialGraded.Quotient.ParameterPostcomposition
- InfinityCategories.Derived.ClosureFunctoriality.All
- InfinityCategories.Derived.CoherentBar.Compact.ConeDerivedEquivalence
- InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonCriterion
- InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonFamilyLift
- InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonNative
- InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonNativeComposition
- InfinityCategories.Derived.CoherentBar.Compact.QuotientParameterLaws
- InfinityCategories.Derived.CoherentBar.Compact.SphereClosureEdgeIsoAdapter
- InfinityCategories.Derived.CoherentBar.Compact.SphereClosureKernelHom
- InfinityCategories.Derived.CoherentBar.Compact.SphereClosureKernelMap
- InfinityCategories.Derived.CoherentBar.Compact.SphereClosureNativeComparison
- InfinityCategories.Derived.CoherentBar.Compact.SuspensionCompositionConeComparison
- InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeComparisonCore
- InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeRepresentativeComparison
- InfinityCategories.Derived.CoherentBar.Compact.SuspensionFixedCoherenceTypes
- InfinityCategories.Derived.CoherentBar.Compact.SuspensionFixedStrictLaws
- InfinityCategories.Derived.CoherentBar.Compact.SuspensionModuleCompositionIso
- InfinityCategories.Derived.CoherentBar.Compact.SuspensionUnitConeComparison
- InfinityCategories.Derived.DGGluingCellProjectiveInput
- InfinityCategories.Derived.DGKappaNativePFamily
- InfinityCategories.Derived.DGKappaSphereClosureSemifreeCovers
- InfinityCategories.Derived.DGKappaSuspensionCanonicalMapData
- InfinityCategories.Derived.DGSuspensionCoherentSquareInput
- InfinityCategories.Derived.DGSuspensionNativeNaturalityModel
- InfinityCategories.Derived.DGSuspensionNativeSquareModel
- InfinityCategories.Derived.DGSuspensionNativeSquareReplacement
- InfinityCategories.Derived.KappaPerfect.SphereClosureCompactComparison
- InfinityCategories.Derived.KappaPerfect.SphereClosureInput
- InfinityCategories.Derived.SuspensionAction.All
- InfinityCategories.F1.Diagrams.NativeTriangleSupplyAll
- InfinityCategories.F2.FilteredExchange.PiCriterion.All
- KST.Fibration.Relative.ClosedStableAll
- KST.LocalizingInvariants.CoreFlag.All
- KST.LocalizingInvariants.CoreFlag.KanPullbackAll
- KST.SConstruction.OdotTailAll
- KST.Spectra.D3All
- KST.Spectra.D3TailAll
- KST.Spectra.S3All

### 6.2 削除（現行一覧にあるが監査から消えた）
- BhattScholze.Delta.DividedPower.DeltaDividedPowerCoefficientImage
- BhattScholze.Delta.DividedPower.DeltaDividedPowerCoefficients
- BhattScholze.Delta.DividedPower.DeltaDividedPowerExpansion
- BhattScholze.Delta.DividedPower.DeltaDividedPowerIdeal
- BhattScholze.Delta.DividedPower.DeltaDividedPowerStep
- BhattScholze.Delta.DividedPower.DeltaDividedPowers
- BhattScholze.Delta.DividedPower.DeltaFactorialDivision
- BhattScholze.Delta.DividedPower.DeltaPDivisionDerivedUnit
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorial
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialDPMorphism
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialDelta
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialDeltaMap
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialFunctorial
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialIdeal
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialMap
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialPDLift
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialPDTarget
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialPDUniversal
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialStable
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialStructure
- BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialSubring
- BhattScholze.Delta.DividedPower.DeltaPDivisionFirstRelationRegular
- BhattScholze.Delta.DividedPower.DeltaPDivisionFrobeniusShift
- BhattScholze.Delta.DividedPower.DeltaPDivisionFrobeniusShiftDerived
- BhattScholze.Delta.DividedPower.DeltaPDivisionFrobeniusShiftTorsion
- BhattScholze.Delta.DividedPower.DeltaPDivisionLocalization
- BhattScholze.Delta.DividedPower.DeltaPDivisionRawMinimal
- BhattScholze.Delta.DividedPower.DeltaPDivisionUnit
- BhattScholze.Delta.DividedPower.DeltaPDivisionWittResidueEvaluation
- BhattScholze.Delta.DividedPower.DeltaPDivisionWittResidueSolution
- BhattScholze.Delta.DividedPower.PrincipalDPBaseChange
- BhattScholze.Delta.DividedPower.PrincipalDPBaseChangeUniversal
- BhattScholze.Delta.DividedPower.PrincipalDPCompletionModP
- BhattScholze.Delta.DividedPower.PrincipalDPEvaluationTensor
- BhattScholze.Delta.DividedPower.PrincipalDPFactorialEquiv
- BhattScholze.Delta.DividedPower.PrincipalDPFactorialKernel
- BhattScholze.Delta.DividedPower.PrincipalDPModP
- BhattScholze.Delta.DividedPower.PrincipalDPPresentation
- BhattScholze.Delta.DividedPower.PrincipalDPQuotientFlat
- BhattScholze.Delta.DividedPower.PrincipalDPRegular
- BhattScholze.Delta.DividedPower.PrincipalDPRelativeCompletionModP
- BhattScholze.Delta.DividedPower.PrincipalDPRelativeDerivedModP
- BhattScholze.Delta.DividedPower.PrincipalDPRelativeModPKoszul
- BhattScholze.Delta.DividedPower.PrincipalDPToFactorial
- BhattScholze.Delta.DividedPower.RankOneDPAnyBasis
- BhattScholze.Delta.DividedPower.RankOneDPBaseChange
- BhattScholze.Delta.DividedPower.RankOneDPBaseChangeUniversal
- BhattScholze.Delta.DividedPower.RankOneDPBasis
- BhattScholze.Delta.DividedPower.RankOneDPCharacteristicCompletion
- BhattScholze.Delta.DividedPower.RankOneDPDerivedFactorization
- BhattScholze.Delta.DividedPower.RankOneDPDerivedKoszul
- BhattScholze.Delta.DividedPower.RankOneDPDerivedRelativeFlat
- BhattScholze.Delta.DividedPower.RankOneDPEnvelopeBaseChange
- BhattScholze.Delta.DividedPower.RankOneDPEnvelopeCoefficientFlat
- BhattScholze.Delta.DividedPower.RankOneDPEnvelopeFree
- BhattScholze.Delta.DividedPower.RankOneDPEvaluatedDerivedFlat
- BhattScholze.Delta.DividedPower.RankOneDPEvaluatedEnvelope
- BhattScholze.Delta.DividedPower.RankOneDPPolynomialAction
- BhattScholze.Delta.DividedPower.RankOneDPPrimeBasis
- BhattScholze.Delta.DividedPower.RankOneDPPrimeBlockBasis
- BhattScholze.Delta.DividedPower.RankOneDPPrimeBlocks
- BhattScholze.Delta.DividedPower.RankOneDPQuotientToEnvelope
- BhattScholze.Delta.DividedPower.RankOneDPTensorRelations
- BhattScholze.Delta.DividedPower.RankOneDPTruncatedAction
- BhattScholze.Delta.DividedPower.RankOneDPTruncatedFree
- BhattScholze.Delta.DividedPower.RankOneDPTruncatedTensorFlat
- BhattScholze.Delta.DividedPower.RankOneDPTruncationDerived
- BhattScholze.Delta.DividedPower.RankOneDPTruncationQuotient
- BhattScholze.Delta.DividedPower.RegularPrincipalDPBaseChange
- BhattScholze.Delta.DividedPower.RegularPrincipalDPModP
- BhattScholze.Delta.DividedPower.RegularPrincipalDPModPFlat
- BhattScholze.Delta.DividedPower.RegularPrincipalDPUniversal
- BhattScholze.Delta.Division.DeltaAdjoinDivision
- BhattScholze.Delta.Division.DeltaAdjoinDivisionEmpty
- BhattScholze.Delta.Division.DeltaAdjoinDivisionFiniteColimit
- BhattScholze.Delta.Division.DeltaAdjoinDivisionFiniteColimitEquiv
- BhattScholze.Delta.Division.DeltaAdjoinDivisionFiniteSystem
- BhattScholze.Delta.Division.DeltaAdjoinDivisionReindex
- BhattScholze.Delta.Division.DeltaAdjoinDivisionReindexFunctorial
- BhattScholze.Delta.Division.DeltaAdjoinDivisionSum
- BhattScholze.Delta.Division.DeltaDivisionClassicalCompletion
- BhattScholze.Delta.Division.DeltaDivisionPDCompletion
- BhattScholze.Delta.Division.DeltaDivisionQuotient
- BhattScholze.Delta.Division.DeltaPTorsionReduction
- BhattScholze.Delta.Division.DeltaTorsionReduction
- BhattScholze.Delta.Division.Relations.DeltaAdjoinDivisionFamilyRegular
- BhattScholze.Delta.Division.Relations.DeltaDivisionEvaluationFamilyStep
- BhattScholze.Delta.Division.Relations.DeltaDivisionEvaluationSource
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteEvaluationRelations
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteGeneratorConstant
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteGeneratorResidue
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteLeadingLinear
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteNormalizedPresentation
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteNormalizedStep
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteRelationPolynomial
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteResidueRelation
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteTopCoefficient
- BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteTopDerivative
- BhattScholze.Delta.Division.Relations.DeltaDivisionFirstOrderNormalForm
- BhattScholze.Delta.Division.Relations.DeltaDivisionFirstResiduePowerPresentation
- BhattScholze.Delta.Division.Relations.DeltaDivisionFirstResiduePresentation
- BhattScholze.Delta.Division.Relations.DeltaDivisionIteratedRelations
- BhattScholze.Delta.Division.Relations.DeltaDivisionResidueRelation
- BhattScholze.Delta.Division.Relations.DeltaDivisionSecondFinitePresentation
- BhattScholze.Delta.Division.Relations.DeltaDivisionSecondFiniteResidueRelation
- BhattScholze.Delta.Division.Relations.DeltaDivisionSecondMonicPresentation
- BhattScholze.Delta.Division.Relations.DeltaDivisionSecondPowerPresentation
- BhattScholze.Delta.Division.Relations.DeltaDivisionSecondResidueRelation
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceAlgebras
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceCoefficientMaps
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceCoefficientQuotients
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceCoefficientReduction
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceCoefficientRightFactor
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceCoefficientTor
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceTensor
- BhattScholze.Delta.Division.Relations.DeltaDivisionSourceTensorDelta
- BhattScholze.Delta.Division.Relations.DeltaDivisionUnitDenominator
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittFiniteRelationIdeal
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittJetRegularity
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittJetRelations
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittMonicRelations
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittNormalizedIdeal
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittNormalizedQuotient
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittNormalizedRelation
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittPolynomialRelations
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittRelationElement
- BhattScholze.Delta.Division.Relations.DeltaDivisionWittRelationIdeal
- BhattScholze.Delta.Division.Relations.RelativeFreeSubsetSplit
- BhattScholze.Delta.Division.Relations.WittDivisionPolynomialRemainder
- BhattScholze.Delta.Division.Relations.WittDivisionTriangular
