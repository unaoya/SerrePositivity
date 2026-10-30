# LengthAlgebra・IntersectionMultiplicity の整理計画（2026-10-30）

概要：論文の層の見直しのうち、`SerrePositivity/LengthAlgebra/`（58 ファイル、約 6400 行）と `SerrePositivity/IntersectionMultiplicity/`
（21 ファイル、約 3300 行）について、ファイルの統合、死んだファイル・未使用の削除、重複の一本化、Mathlib への置き換え、層の修正をまとめる。
二つは PerfectComplex（正規化された長さ・Euler 標数）と層が入り組んでいるので一つの計画にした。調査（2026-10-30、読むだけ）の結果を元にした
計画で、実作業はまだ行っていない。
方針：作業の決まりは [commutative-algebra-refactor-plan.md](commutative-algebra-refactor-plan.md) の §2 と同じ。PerfectComplex 側は
[perfect-complex-refactor-plan.md](perfect-complex-refactor-plan.md) と合わせて決める。
規約：Mathlib の確認は固定版（2026-10-07）と最新版（2026-10-28）の両方で行い、差はなかった。`sorry`・`axiom`・`maxHeartbeats` の引き上げはない。
使われ方：作業を再開するときの手順書。

## 1. 中身と外への影響

- **LengthAlgebra（LA）**：正規化された長さ λ（`NormalizedLength`、定義は PerfectComplex/NormalizedLength）の理論。Serre 商、almost 長さ、
  商の長さの評価、Koszul・錐・完全複体の λ-Euler 標数、根の塔の長さ（RootTowerLength/）。
- **IntersectionMultiplicity（IM）**：Serre の `chi` とその基本 API（同値・可換性・加法性・基底変換・dévissage・有限拡大・分解による評価）、
  Adams 作用による消滅、等標数 0 の対角環による正値性、パラメータ商の Tor。
- **BS は LA・IM を import しない。** CLMST は LA を多く import する（AlmostBaseChange・AlmostQuotientAction・AlmostVanishing・
  CyclicPowerReduction・GeometricDecay・QuotientPowerBound・Koszul{CokernelBounds,ErrorEuler,EulerComparison,EulerZero,Restriction,
  ZeroMonotonicity}・RootTowerLength/{CompletedNormalized,CompletedFiniteLength,CompletedQuotientEvaluation,CompletedTensorEvaluation,
  CoordinateModuleVanishing,CoordinateVanishing,StageDecay}。import なしで名前を使うもの：ShortExactEuler・HomologyExactBounds・
  ConeCompositionEuler・ConeHomologyLength）。これらは名前を残し、CLMST の import 行を書き換える。IM の利用者は Paper・Inputs・Asymptotic・
  CommutativeAlgebra/Koszul/RegularEuler・PerfectComplex/TensorTorComparison（BS/CLMST なし）。

## 2. 層の問題（最初に解く）

1. **LA と PerfectComplex が入り組んでいる**：PC/NormalizedEuler が LA.ExactSequenceEuler を import し、それが LA.SerreQuotient を経て
   PC.NormalizedLength を import する。PC/KoszulLengthBounds は LA.HomologyExactBounds を import する。一方で LA の大半は PC/NormalizedEuler を
   import する。→ PC/NormalizedLength と LA の Serre 商の核（SerreQuotient・ExactSequenceEuler・ShortExactEuler・HomologyExactBounds）を
   一つの低い層（例 `LengthAlgebra/Core`、または PerfectComplex の下の `NormalizedLength/`）にまとめ、PC/NormalizedEuler はその上に置く。
2. **CA/Koszul/RegularEuler → IM.ResolutionEvaluation**（B2 で作ったファイル）：`koszulEulerChar_eq_chi`・
   `chi_eq_finrank_mul_length_of_resolution` を使う。ResolutionEvaluation の前半（60–280 行、`chiLam`・`chiOrd`・ひねりの補題）は
   PerfectComplex の内容なので PerfectComplex へ移し、`chi` の部分だけを IM に残す。そのうえで RegularEuler を IM の上へ上げるか、使う 2 補題を下ろす。
3. **PC/TensorTorComparison → IM.Basic**（`chiOrd_tensorResolution`）：`chi`（Basic、50 行）を HomologicalAlgebra/Tor の近くへ下ろせば解消。
4. **CA/KoszulMultiplicity/Formula → LA.ConeCompositionEuler**（`lambdaEuler_scalarCone_pow`）：ConeCompositionEuler を Core 側へ。
5. LA/Flat → IM.NormalizedTor、IM/ParameterQuotientTorBound → LA.PerfectVanishing：NormalizedTor（λ 長さの Tor）は LA へ移す。
6. `Inputs/IntersectionTheory` は包み：`Inputs.regularResolution` は `SerrePositivity.regularResolution`、`Inputs.intersectionVanishing` は
   `intersectionVanishing_of_adams` の重複。インライン化し、IM/Additivity・FiniteExtension の import を張り替える。

## 3. LA の統合（58 → 約 14 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| Core（低い層、§2.1） | SerreQuotient・ExactSequenceEuler・ShortExactEuler・HomologyExactBounds（＋PC/NormalizedLength を合わせる案） |
| Almost | AlmostQuotient・AlmostBaseChange・AlmostQuotientAction・AlmostVanishing・CyclicPowerReduction（CLMST が使う） |
| QuotientBounds | GeometricDecay・QuotientPowerBound・QuotientBounds・FinitelyGeneratedFiniteLength・Nontrivial |
| Cone | ConeHomologyLength・ConeCompositionEuler・KoszulHomologyLength |
| KoszulModule | KoszulCokernelBounds・KoszulErrorEuler・KoszulEulerComparison・KoszulEulerZero・KoszulRestriction・KoszulZeroMonotonicity（CLMST が使う） |
| Koszul | Koszul・Ordinary・OrdinaryKoszulEuler・Comparison・KoszulFormula |
| Perfect | PerfectHomology・PerfectVanishing・PerfectBaseChange |
| Flat | Flat・CohenMacaulay、IM の NormalizedTor |
| RootTowerLength/Basic | Defs・FiniteStage・FiniteGeneration |
| RootTowerLength/Additivity | AdditivityApproximation・AdditivityFinite・AdditivityFinitelyGenerated・Normalized |
| RootTowerLength/Completion | Completion・Completed*（CLMST が使う） |
| RootTowerLength/Coordinate | Coordinate*（CLMST が使う） |

- StageDecay は `stageRank` についての ENNReal の計算だけで RootTower.Basic しか import しない → CommutativeAlgebra/RootTower へ（CLMST が使う）。
- 名前空間が `LengthAlgebra`・`SerrePositivity`・`NormalizedLength`・`RootTowerLength`・`Section2`（論文の節の名前、RootTowerLength の
  Defs・FiniteStage・FiniteGeneration・Additivity*・Completion）と混在。`LengthAlgebra` と `LengthAlgebra.RootTower` にそろえる
  （CLMST が使う名前は参照の書き換えで追う）。
- 再エクスポートだけのファイル：LA/Foundations（importer はルートだけ）、HomologicalAlgebra/KoszulHomologyLength（LA.KoszulHomologyLength の
  再エクスポート）。どちらも削除。

## 4. IM の統合（21 → 約 7 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| Basic | Basic・Equivalence・BaseChange（§2.3 で `chi` を下ろすなら HomologicalAlgebra/Tor 側へ） |
| Additivity | Additivity・Devissage・FiniteExtension |
| Vanishing | AdamsVanishing・AdamsVanishingTwo・AdamsVanishingThree・AdamsVanishingAll・CubicCyclotomicBaseChange（一本の鎖、約 200 行） |
| EqualCharZero/Ring | DiagonalRing・DiagonalFlat |
| EqualCharZero/Tor | DiagonalTor・DiagonalDimension |
| EqualCharZero/Positivity | DiagonalPositivity・EqualCharZeroPositivity |
| ParameterQuotient | ParameterQuotientTor・ParameterQuotientTorBound |
| ResolutionEvaluation | `chi` の部分（280–488 行）だけ。前半は PerfectComplex へ（§2.2） |

## 5. 死んだファイル・未使用

- **LA の死んだ連鎖（約 880 行）**：Foundations（再エクスポート）、EulerCompatibility（外の利用なし）、FlatRealization（3 定理とも未使用。
  Paper/Section4/FlatRealization は import するが LA.Flat しか使わない）、それだけが使う PerfectMinimalLowerBound → PerfectLowerBound →
  PerfectHomologyComparison → FiniteQuotientEquivalence → FiniteQuotientComparison。生きている版は PerfectComplex/MinimalLowerBound・
  Asymptotic/PaperMinimalLowerBound・Paper/Section4/FlatRealization。PerfectVanishing は Asymptotic/RankVanishing と ParameterQuotientTorBound
  が使うので残す。
- **AlmostFactorQuotient**：importer なし。`scripts/audit_clmst.lean` だけが import して 2 定理を確かめている。監査の行と一緒に削除。
- 未使用の宣言：IM の `quotDiagEquiv_mk`（simp）・`fwd_tmul`。LA の `length_eq_of_full_almost_iso`、CohenMacaulay の `koszulFinite_of_cm`・
  `koszulEuler_of_cm`・`tor_length_of_cm`（使われているのは `koszulAcyclic_of_cm` だけ）、`flat_rank_iff_koszul`、`perfectBaseChangeHomology`、
  `perfectEuler_triangle`、`towerLengthFun_eq_iSup_of_directed_union`、`towerLengthFun_add_of_exact_of_finitelyGeneratedExact`、
  `tower_baseChange_shortExact`、`towerLengthFun_add_of_exact_finitePresentation`、`completedNormalizedLength_restrictScalars`、
  `coordinateZeroExponent_at`（simp）、`presentedLength_congr`、`subsingleton_tensorProduct_of_right`、`finiteLengthQuotient_isZero_iff`、
  `extendedQuotientLength_obj`（simp）。
- ファイルの中だけで使われている約 120 の名前は private に（ParameterQuotientTor 23、DiagonalDimension 14、RootTowerLength/FiniteStage 14、
  DiagonalTor 11、DiagonalRing 9、FiniteExtension 7 など）。

## 6. Mathlib との重なり

- Mathlib には交点重複度・Serre の Tor 公式・Koszul 複体・長さで値を取る Euler 標数がない。`HomologicalComplex.eulerChar` は finrank 版で代わりにならない。
- `quotEquivOfKerEq` は `Submodule.quotEquivOfEq ≪≫ quotKerEquivOfSurjective`（確度高、インライン化）。
- `isUnit_two_of_residue_ne_zero` は `IsLocalRing.residue_ne_zero_iff_isUnit` から直接（確度高）。
- `subsingleton_tensorProduct_of_right`（RootTowerLength/Defs）は `inferInstance`（確度高、削除）。
- `tensorQuotQuotEquiv`（A/I ⊗ A/J ≃ A/(I⊔J)）は `TensorProduct.quotientTensorQuotientEquiv` と商の同一視の合成（確度中）。
- 通常の長さの加法性は `Module.length_eq_add_of_exact`（`module_length_add` は λ 版なので別）。

## 7. 一本化

- **Euler 標数の種類**：`chi`（IM、ℤ、Tor）、`chiOrd`・`chiLam`（PC/Basic）、`lambdaEuler`（PC/NormalizedEuler）、`perfectEuler`（LA/PerfectHomology）、
  `koszulEuler`（LA/Koszul）、`koszulEulerChar`（CA/Koszul.lean）、`homologyLengthSum`（CA/Length/Euler）。橋渡しの補題が散らばっている：
  `ordinary_koszulEuler_eq_koszulEulerChar`（LA/OrdinaryKoszulEuler）、`koszulEulerChar_self`・`koszulEulerChar_eq_chiOrd_of_residue_surjective`
  （CA/KoszulMultiplicity/Formula）、`koszulEulerChar_eq_chi`（IM/ResolutionEvaluation）、`chiOrd_eq_alternating_term_lengths`（CA/Length/Euler）。
  → 比較のファイル 1 本（層の順で一番上に置ける場所、例 `LengthAlgebra/EulerComparison`）に集める。定義の種類を減らせるかは PerfectComplex の
  計画と合わせて検討する。
- `isFiniteLength_torModule_of_finite_free_left`・`chi_of_finite_free_left`（ResolutionEvaluation）は `length_tensorProduct_of_finite_free_left`
  （CA/Length/Basic）と並行。
- `torModule_eventually_subsingleton`（IM/Additivity）は Inputs/IntersectionTheory・HomologicalAlgebra/TorFiniteLength の Tor の消滅と重なる。
- LA の almost 長さ（Almost*）は CommutativeAlgebra/Almost/SerreComparison・CLMST/AlmostLength・NormalizedAlmostLength と並行。CLMST の計画
  （[clmst-refactor-plan.md](clmst-refactor-plan.md)）で CLMST 側の特殊化を LA へ寄せる。
- `chi_rank_factor_{left,right}_of_additivity_and_vanishing` は 3 つの等式を仮定に取って書き換えるだけ。インライン化。

## 8. その他

- FiniteExtension の docstring が「Inputs の名前付きの未証明定理」と書いているが、今は `intersectionVanishing_of_adams` で証明済み。直す。
- 一般的すぎる名前：`SerrePositivity.chi`、`ParamQuot.{B, IC, U, T1, T2, fwd, bwd, ψ}`、`TorBound.Kills`、`TorClaim`、`module_length_add`、
  `koszulScalars`、`DiagonalRing.{eval, var, const, diag}`。
- IM の Adams のファイルは英語の docstring、他は日本語。統合のときに日本語の形式（概要・方針・規約・使われ方）にそろえる。
- `backward.isDefEq.respectTransparency false` が約 20 ファイル、`backward.defeqAttrib.useBackward true` が IM の Adams・FiniteQuotientEquivalence・
  CubicCyclotomicBaseChange に。統合のときに外せるか試す。

### 提出候補

Serre の交点重複度 `chi`（`chi_eq_sum_range`、`chi_congr`・`chi_comm`、各変数での加法性、平坦な局所基底変換）、`IsLocalHom (MvPowerSeries.C)`、
`tensorQuotQuotEquiv`（Mathlib の合成がなければ）、`sum_Icc_negOnePow_eq_sum_range`、ENNReal の幾何的な減衰（`ennreal_eq_zero_of_geometric_bound`、
一般的な名前のまま ENNReal のファイルへ）、`radical_eq_maximalIdeal_of_length_ne_top`。

## 9. 順序

1. 死んだ連鎖・未使用・再エクスポートの削除、確度高の Mathlib への置き換え（CLMST の参照なし）。
2. 層の問題（§2）。PerfectComplex の PC1（Basic・NormalizedLength）と同じ全依存ビルドにまとめる。
3. 統合（§3・§4）。CLMST が import する LA のファイルの移動は import 行の書き換えだけで済む（許可済みの範囲）。
4. Euler 標数の比較の一本化（§7）。
