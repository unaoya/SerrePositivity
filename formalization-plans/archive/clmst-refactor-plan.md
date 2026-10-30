# CLMST の整理計画：基礎と論文の分離（2026-10-30）

概要：`SerrePositivity/CLMST/`（146 ファイル、約 12300 行。Prop247* 57 本・約 4400 行、その他 89 本・約 7900 行）を、共有層へ下ろすべき
**基礎（A）**と、論文 CLMST の主張とその証明の足場である**論文（B）**に分ける。A は可換環論・ホモロジー代数・almost 数学・完全環と
perfectoid・長さ・Koszul・Tor の一般論。B は Prop 2.4.7・Thm 4.0.3(a)・Cor 4.0.4・Prop 4.0.10・Prop 4.0.14・Claim 4.0.15 とその系。
調査（2026-10-30、読むだけ）の結果を元にした計画で、実作業はまだ行っていない。
方針：CLMST・BhattScholze は BS のセッションの管轄なので、実際の移動は
[homological-algebra-refactor-plan.md](homological-algebra-refactor-plan.md) §8 の 5 で決めた「第二層の作業時間」（BS 側の編集を止めて
まとめて行う時間）に行う。BhattScholze に依存する A は **BhattScholze/ の下に置く**（案 a、2026-10-30 決定）。CommutativeAlgebra には
BS に依存しないものだけを残し、層を BS < CLMST の一方向にそろえる（CA 計画 §8 の H 群の「層の逆転の解消」と同じ方針）。
規約：CLMST の形式化は 2026-10-17 に完了している（[clmst.md](clmst.md)）。`sorry`・`axiom`・`maxHeartbeats` の引き上げはない。
使われ方：第二層の作業時間に使う手順書。

## 1. 分類の結果

| | ファイル | 行 |
| --- | --- | --- |
| A（基礎） | 58（Prop247 20、その他 38） | 約 4200 |
| M（混在、A の部分を下ろし B を残す） | 19（Prop247 7、その他 12） | 約 2300 |
| B（論文） | 69（Prop247 30、その他 39） | 約 5700 |

- A のうち **BS より下へ下ろせる**もの：約 35 本・2000 行以上（§2.1）。
- A のうち **BS に依存する**もの：約 30 本（§2.2）。BhattScholze/ の下へ。
- CLMST の外で使われる名前：`proposition_2_4_7_proved`（CLMST/Inputs/PerfectoidIsogeny が包む）、Paper/Section2/MixedPerfectoid が再エクスポート
  する `Section2.MixedPerfectoid` 一式、BS/Almost/PerfectoidAlmost が使う `CLMST.perfectoidIdealMod`、`Inputs/CLMST.lean` 経由の主定理。
- `scripts/audit_clmst.lean`（1428 行、`CLMST.` の参照 195）・`audit_clmst_b3.lean`・`scripts/audit/clmst.lean` が古い名前とパスを固定している。
  移動・改名のたびに直す（許可済みの範囲）。

## 2. 基礎（A）の行き先

### 2.1 BS より下へ（CommutativeAlgebra・HomologicalAlgebra・LengthAlgebra）

| 行き先 | 元（CLMST/ からの相対） | 注意 |
| --- | --- | --- |
| CA/EtaleRankStratification（新設） | Prop247RankLoci・RankTransport・RankPrincipal・RankProduct・RankProductAway・RankBaseChange、Prop247RankImages の `rankOpen*` | Mathlib：`awayRank_isLocallyConstant` = `Module.isLocallyConstant_rankAtStalk`（確度高）、`awaySpectrumHomeomorph` は `localization_away_isOpenEmbedding`＋`localization_away_comap_range`（確度高）、階数の基底変換は `Module.rankAtStalk_baseChange`（確度中〜高）、`rankOpen_exists_basicOpen` は `existsUnique_idempotent_basicOpen_eq_of_isClopen`（確度中） |
| CA/ReducedFiniteFreeIsogeny 付近 | Prop247RankCone（R → ∏ R_n の錐が g の冪で消える） | HA/TwoTermConeAnnihilator を使う |
| CA/IntegralAwayExtension | Prop247RankValuation（死んでいる、§4）・Prop247FiniteComparisonValuation（付値環への一意な拡張） | |
| CA/ReducedSectionImage 付近 | Prop247RankImages の `openSectionImage*`・`toOpenSectionImage*` | `zeroLocus_vanishingIdeal_eq_closure`（部分的） |
| CA/FinitePresentationIsogenyLift | Prop247FiniteFreeComparison、Prop247CommonSquare（局所化した分解） | FiniteFreeConeIsogeny を先に下ろす |
| CA/RootTower/BaseChange（新設） | StageAlgebra の `StageAlgebra`・instance・`stage0*`、StageBaseChange・StageDimension・StageFiniteness・StageLocality・StageResidueLength・StageParameterChange・CompletedStageBaseChange・StagePowerMembership、StageTensor の `stageToCompletedTower`・`stageToCompletedTensor` | BS への依存は StageAlgebra → CLMST.Algebra 経由だけ。StageAlgebra を分ければ外れる。`stageAlgebraIsNoetherianOfBase` は優先度 90 の大域 instance |
| CA/RootTower/ModP* の隣 | StageModPImageLength・StageModPLengthBound | |
| CA/RootTower/Roots 付近 | PerfectoidIdealRoots の `completedTowerRoot*`、PerfectoidFrobeniusComparison の塔の部分 | |
| CA/GenericEtale | EtaleLocus（`exists_finite_etale_away_of_charZero` の 1 行の包み、インライン化） | |
| CA/RegularLocalRing・FrobeniusHypersurfaceGrowth | ModPHypersurfaceGrowth、RPerfdCohomologyInputs の `parameter_power_isKoszulResolution` | |
| CA（局所化の共通模型、E 群） | PerfectoidEtaleCommonCover・PerfectoidFinitePresentationCommonModel | |
| CA/PrincipalMaximalFactorization | CyclicFactorReduction の `exists_p_power_factor_of_nonzero`・`exists_p_power_unit_of_fin_one`（包み） | |
| CA/AlgebraMapCokernel | PerfectoidCokernel の `PerfectoidizationCokernel`・`…RestrictEquiv`・`*_shortExact` | 零化の補題は B（Prop 2.4.7 を使う） |
| HA/TwoTermConeAnnihilator | FiniteFreeConeIsogeny（Claim 2.4.8 の一般形） | |
| HA/CompleteFaithfullyFlatDescent | IsogenyDescent（完全忠実平坦な拡大に沿った錐のスカラーの降下）、`moduleMapConeBoundedAbove` は HA/DerivedModuleCone へ | ConeComparison を動かす前提 |
| HA/DerivedCompletion | Prop247RankCompleteness（→ ModuleClosure）・Prop247ConeComparison（→ CompletedBaseChangeTriangle）・Prop247SourceComparison（→ CompletedFlatBoundedComparison）、Prop247Cone の `prop247_source_isModuleComplete`・`cone_isComplete_of_perfectoid_target`（→ FinitePresentationComplete）、Prop247Uniform の `prop247_uniform_reductions_of_fixed_cone`、ModuleCompletion（死んでいる） | |
| LA/Almost* | AlmostLength（`length_eq_of_(full_)almost_iso_baseChange` の特殊化、インライン化）、NormalizedAlmostLength の一般部分 | |
| LA/RootTowerLength/CompletedQuotientEvaluation | RootFiltrationBound の `completedLength_quotient_le_root_factor*` ほか 3 つ | |

- Mathlib への置き換え：`iterate_pow_apply` = `congrFun (pow_iterate p m) x`、`pow_sub_mem_of_sub_mem` は `sub_dvd_pow_sub_pow` から（ともに確度高）。

### 2.2 BhattScholze/ の下へ（BS に依存するもの）

| 行き先 | 元 |
| --- | --- |
| BS/Almost/PerfectoidAlmost | BasicSetup、Inputs/BasicSetup（`perfectoidIdealMod_idempotent`、重複、§3）、Almost（`perfectoidIdealMod` ほか。§5 の逆転を解消） |
| BS/Almost（新 PerfectoidIdealTor） | PerfectoidIdealCompletedMul、PerfectoidIdealTorCover・TorRoots・TorTransport・TorComparison・ExcisionTor、KLAicTorFromExcision の A 部分 |
| BS/Andre | AndreTorDescent・AndrePerfectoidizationTorDescent・AndrePerfectoidIdealTorDescent、Prop247AndreBase（→ AndreFlatness） |
| BS/Perfectoidization（Excision など） | PerfectoidizationExcisionComparison・PerfectoidizationImageTorComparison・PerfectoidFiniteProductTor・CanonicalExcisionTorInput・KLFiniteComparisonExcision（BS Cor 8.12 による excision。今は B の KLCohomologyFromExcision を import しているので先にほどく）・KLOriginalTorFromExcision・KLCanonicalSingleTriangleBridge の A 部分、PerfectoidizationCone、TensorOrder の `IsPerfectoidization.comp_ringEquiv` |
| BS/Semiperfectoid | Prop247IdempotentQuotient（完全環を冪等元で割っても perfectoid）・Prop247QuotientPerfectoidization（→ Surjectivity）・Prop247ProductComponents・Prop247ProductUniversality・Prop247ProductPerfectoid（死んでいる）・Prop247RankProductUniversality の A 部分 |
| BS/Perfectoidization/CompletedTensor・CompletedBaseChange | Prop247TensorUnit・Prop247TargetComparison（`prop247_targetTensorAlgEquiv` は `.choose` でデータを作っている。持ち上げの def に） |
| BS（perfectoid イデアルの根） | PerfectoidIdealRoots の `perfectoidQuotient`・`perfectoidIdealQuotientEquiv`・`mem_perfectoidIdeal_of_pow_mem_span*` など、PerfectoidFrobeniusComparison の一般部分（`quotientRootFrobenius*`・`root_mem_sup_*` など）、CyclicFactorReduction の `perfectoidIdeal_le_of_p_power_factor` |
| HA/DerivedCompletion/PowerTorsionTorExtension | AllModuleAlmostTor（`tor_eq_zero_of_power_torsion_and_complete_extensions` の 1 行の包み、死んでいる） |
| 共有の対象（Paper と CLMST） | Algebra の `Section2.MixedPerfectoid`・`toMixedPerfectoid`・`isPerfectoidization_toMixedPerfectoid` と instance → BS 側の根の塔の perfectoid 化（例 `BhattScholze/…/RootTowerPerfectoidization`）。`CLMST.RPerfd`（その別名）は B に残す |

- BS に依存する A を CA に置かない方針なので、CA にすでにある BS への依存（PerfectoidIdeal 系・AbsolutelyIntegrallyClosedPerfectoidQuotient・
  MonicRelationRegularSequence など、CA 計画 §8.1）も同じ作業時間に BS 側へ移す。
- `prop247_` の接頭辞は一般の事実にも付いている（`prop247_isIntegralPerfectoid_idempotent_quotient`・`prop247_completion_unit_surjective`・
  `prop247_awaySpectrumHomeomorph` など）。下ろすときに数学の内容の名前へ改名する。

## 3. 論文（B）の構成

Prop 2.4.7 の証明の骨組み（実際に使われている経路）：
`proposition_2_4_7_proved` → `prop247_isogeny_of_specified`（Proof：BS Cor 8.12 の excision に完備性 RankClosedSides と付値の拡張
RankSourceValuation・FiniteComparisonValuation を与える）← 一般階数の降下 `prop247_exists_canonical_generalRank_descent_data`
（CanonicalRankDescent ← GeneralRank・AndreBase・RankData・RankProductUniversality・CoveredDescent）← RankData ← RankComponentExcision
（各階数の成分に定数階数の結果を適用。RankAIC・AicRankAssembly ← AicRankCoefficients ← AicRankImages・RankBaseChangeDiagram・RankCone）。
定数階数：ConstantRankExcision ← ExcisionLocal ← LocalComparison（CommonSquare＋Uniform）。降下の背骨：CoveredDescent ← UniformStandard ←
StandardCone ← StandardSquare（SourceComparison・TargetComparison・TensorUnit・ConeComparison・Uniform）← IsogenyDescent（D1–D6）。

| 新しいファイル | 元 |
| --- | --- |
| Prop247/Descent/Uniform | Uniform（B 部分）・CoveredDescent・UniformStandard |
| Prop247/Descent/StandardSquare | StandardSquare・StandardCone（A 部分は §2 へ） |
| Prop247/ConstantRank | LocalComparison・ExcisionLocal・ConstantRankExcision |
| Prop247/Rank/Targets | RankTargets・RankAIC |
| Prop247/Rank/Diagram | RankBaseChangeDiagram・RankAssembly |
| Prop247/Rank/AIC | AicRankImages・AicRankCoefficients・AicRankAssembly |
| Prop247/Rank/ComponentExcision | RankComponentExcision・RankData |
| Prop247/Rank/TargetComparison | RankTargetComparison・RankProductUniversality（B 部分） |
| Prop247/Rank/ClosedSides | RankClosedSides・RankSourceValuation |
| Prop247/GeneralRank | GeneralRank・CanonicalRankDescent |
| Prop247/Proof | Proof |
| Prop247/Consequences | PerfectoidIsogeny・Inputs/PerfectoidIsogeny・TensorIsogeny・CompletedTensorIsogeny・NonunitIsogeny、Algebra・StageAlgebra の RPerfd・`toRPerfd` |
| Thm403a | AllModuleTorFromBS・CompletedTowerAllModuleTor・ConditionalCohomologyFromPowerTorsion・KLAllModule（主経路から外れている、§4） |
| Cor404 | ConditionalCohomologyVanishing・FiniteStageKoszulAnnihilator・RPerfdCohomologyInputs（B 部分）・RPerfdTorBaseChange・KLCohomologyFromExcision・Corollary404・CohomologyVanishing・Inputs/CohomologyVanishing |
| Prop4010 | Cyclic*（8 本）・RootFiltrationBound（B 部分）・NormalizedAlmostLength（B 部分）・Inputs/AlmostLength |
| Prop4014 | PerfectoidCokernel（B 部分）・PerfectoidCokernelEuler・CompletedCokernel{Koszul,Length,FiniteEuler}・CompletedSourceLength・SourceEulerEvaluation・CompletedTargetLength・SelectedParameterEuler・CompletedParameterFiniteness |
| Claim4015 | ParameterLastPowerLength・ParameterFormulaDescent・ParameterLength・Inputs/ParameterLength |

- `CLMST/Inputs/` は名前と中身が合っていない（すべて証明済みで引用ではない）。上の表のとおり節のファイルに吸収して Inputs/ をなくす。
- `hetale : letI := GenericEtale.awayAlgebra … Algebra.Etale …` の長い仮定が約 15 の主張で繰り返される。名前付きの述語にする。

## 4. 死んだもの・主経路から外れているもの

- Prop247 の死んだファイル（10 本・676 行。importer はルートと `scripts/audit/clmst.lean` だけ）：ActualDescent・Conditional・CompletedDescent
  （古い「条件付き」の終点）、ConstantRank・ConstantRankDescent・RankDescent（並行していた定数階数の経路）、AicRankValuation・RankValuation
  （RankSourceValuation・FiniteComparisonValuation の重複）、FiniteFreeCover、ProductPerfectoid。
- その他で `Inputs/CLMST.lean` から届かないもの：Thm 4.0.3(a) の全加群版の一群（AllModuleAlmostTor・AllModuleTorFromBS・CompletedTowerAllModuleTor・
  ConditionalCohomologyFromPowerTorsion・KLAllModule）、CompletedCokernelKoszul、KLCanonicalSingleTriangleBridge、ModuleCompletion、
  PerfectoidIdealExcisionTor・PerfectoidIdealTorComparison・PerfectoidIdealTorRoots、TensorOrder、Inputs/AlmostLength。
  **決定（2026-10-30）**：Thm 4.0.3(a) の一群は論文の内容なので残す。残りは A の部分を下ろしたうえで削除（論文の主張を含むものは残す）。
- `corollary_4_0_4` が `CLMST`（Corollary404）と `CLMST.Inputs`（Inputs/CohomologyVanishing）に 2 回定義されている。一つに。
- mod p^N の冪等性の証明が 2 通り（BS 側の `perfectoidIdealMod_idempotent` と `CLMST.Inputs.perfectoidIdealMod_idempotent`）と、BasicSetup の
  `Fact` の包み。一つに（BS 側の名前は `scripts/audit_bhatt_scholze_b5.lean` だけが使う）。
- 不要な import：Corollary404・CyclicLength・Inputs/CohomologyVanishing・Inputs/ParameterLength の `Mathlib.RingTheory.WittVector.Basic`・
  `MvPowerSeries.Basic`。

## 5. 層の逆転 2 か所

- **BhattScholze/Almost/PerfectoidAlmost → CLMST.Almost**：`BhattScholze.perfectoidIdealMod_idempotent` の中で `CLMST.perfectoidIdealMod` を
  使うためだけ。Almost.lean を BS/Almost/PerfectoidAlmost の側へ移せば解消（§2.2）。
- **Paper/Section2/MixedPerfectoid → CLMST.Algebra**：11 行の再エクスポート。`Section2.MixedPerfectoid` 一式を BS 側の根の塔の perfectoid 化へ
  移せば解消。Paper/Section2/MixedPerfectoid は削除して importer を張り替える。

## 6. 順序（第二層の作業時間の中で）

1. CLMST の外で使われる名前を固定（§1）。監査の参照の一覧を取る。
2. BS より下へ下ろす A（§2.1）：BS への依存がないので、CA・HA・LA の対応する群の統合と同時に行える。CLMST の側は import 行と参照の書き換えだけ。
3. BS の下へ置く A（§2.2）と、CA に今ある BS 依存のもの（CA 計画 §8.1）を一緒に BhattScholze/ へ。§5 の逆転を解消。
4. B の統合（§3）、死んだファイルの削除（§4）、`prop247_` の改名。
5. `scripts/audit_clmst*.lean`・`scripts/audit/clmst.lean`・`bhatt_scholze.lean` を直し、全依存ビルド 1 回でコミット（BS/CLMST の分は独立コミット、
   旧→新の対応表を付ける）。

## 7. 決定待ち

1. ~~BhattScholze/ に新しいファイルを置く作業を誰が行うか~~ → コーディネータが第二層の作業時間に行う（BhattScholze/ を編集しない決まりの、この件の例外。2026-10-30）。
2. ~~Thm 4.0.3(a) の全加群版の一群を残すか~~ → 論文の内容なので残す（2026-10-30）。B の Thm403a のファイルにまとめる。
3. ~~B のファイルの名前~~ → 論文の番号ではなく内容の名前を付ける（2026-10-30）。§3 の表の名前（Prop247/…・Thm403a・Cor404・Prop4010・Prop4014・Claim4015）は
   仮の呼び名で、作業時に内容の名前（例：Prop247 → `IsogenyOfPerfectoidization/…`、Prop4010 → `CyclicLengthBound` など）へ置き換える。名前の案は作業前に提示する。
