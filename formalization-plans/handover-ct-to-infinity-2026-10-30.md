# 伝達：CategoryTheory の下位ディレクトリと Nerve まわりの整理を ∞ 基盤の作業へ（2026-10-30）

宛先：∞ 基盤の整備（[infinity-foundation-plan.md](infinity-foundation-plan.md)、Codex の指示書 IF-Wn）を管理している側。
差出：論文の層の整理（[refactor-plan.md](refactor-plan.md)）のコーディネータ。
要旨：論文の層の見直しで CategoryTheory を調べたところ、下位ディレクトリ（104 本）と Nerve まわり（9 本）は ∞ 基盤の側しか使っていないことが
分かった。ユーザーの決定（2026-10-30）により、この整理は ∞ 基盤の指示書に含めて行う。論文の層の側ではこれらのファイルに触れない。
以下は調査結果と、決まっていることの引き渡し。R 番号への採番と、指示書のどの単位に入れるかはそちらで決めてほしい。

## 1. 範囲

- `SerrePositivity/CategoryTheory/` の下位ディレクトリすべて：Monoidal/（67）・Presentation/（15）・Quiver/（7）・Simplex/（6）・Enriched/（3）・
  LiftingProperties/・Limits/・Groupoid/・MorphismProperty/（計 104 本、約 8400 行）。
- トップ階層の Nerve まわり 9 本：NerveHomotopy・NerveHomotopyUniverse・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・
  NerveVertices・SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp。
- トップ階層の再エクスポートの殻 7 本：AnchoredChain*・ArrowContext・LabelledChain・SimplexChainParameter（HomotopicalAlgebra/Rectification を
  再エクスポートするだけ。importer は `scripts/audit/shared.lean`・`scripts/audit_homotopical_foundations.lean` だけ）。
- `Spectra/SymmetricSequence/` の殻 4 本（TensorPowers・TensorPermutations・AdjacentTranspositions・AdjacentBraid、各 10 行で Monoidal/* を再エクスポート）。

利用者はすべて Spectra・HomotopicalAlgebra（主に `HomotopicalAlgebra/GeneralTools` の再エクスポート経由）・EInfinity・KST・InfinityCategories。
**BhattScholze・CLMST・論文の層（Paper・Asymptotic・PerfectComplex・KTheory など）は import も名前の参照もしない。** BS の再ビルドは起きない。

## 2. 決まっていること（ユーザー、2026-10-30）

1. Nerve まわり 9 本を `HomotopicalAlgebra/Simplicial/` の側へ移す。今は NerveVertices が `HomotopicalAlgebra/Simplicial/VertexTuples` を、
   NerveSimplexFirstFunctor が `HomotopicalAlgebra/Simplicial/SimplexNerveAugmentation` を import し、後者は `CategoryTheory/SimplexChainVertices` を
   import していて、二つのディレクトリが互いに依存している。移せば解消する。利用者は HomotopicalAlgebra 14・EInfinity 10・KST 4・CategoryTheory 2。
2. 下位ディレクトリの整理は ∞ 基盤の指示書に含める（論文の層の側では行わない）。

## 3. 調査結果（2026-10-30、読むだけ）

### 3.1 死んだファイル

- Presentation/ の 15 本すべてと Quiver/WeightedPaths・WeightedPathMaps：各 24 行で、同名の `HomotopicalAlgebra/Rectification/CategoryTheory/…` を
  再エクスポートするだけ。importer なし、ルートの `SerrePositivity.lean` にもない。参照は `scripts/homotopical_generalization_manifest.json` だけ。
- §1 のトップ階層の殻 7 本と Spectra の殻 4 本。

### 3.2 統合案（104 → 約 35 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| Monoidal/Mod/Free | FreeModule |
| Monoidal/Mod/Limits | ModuleLimits・ModuleColimits・ModuleTransport |
| Monoidal/Mod/BalancedTensor | BalancedTensor・BalancedTensorModule・BalancedTensorIterated・TensorRightModule |
| Monoidal/Mod/Monoidal | BalancedTensor{Associator,LeftUnit,RightUnit,Triangle,Pentagon,Monoidal} |
| Monoidal/Mod/Symmetric | BalancedTensor{Symmetry,Hexagon,Symmetric} |
| Monoidal/Mod/FreeTensor | BalancedTensorFree{Left,Right,Pair,Unit,Associator}・FreeModuleMonoidal |
| Monoidal/Mod/InternalHom | ModuleInternalHom・…Action・…Functor |
| Monoidal/Mod/InternalHomFree | ModuleInternalHomFree*・…Transport* |
| Monoidal/Mod/Closed | ModuleClosed |
| Monoidal/TensorPower/Basic | TensorPowers・TensorPowerCoherence |
| Monoidal/TensorPower/Permutation | TensorPermutations・AdjacentTranspositions・AdjacentBraid・PermutationAction |
| Monoidal/TensorPower/Blocks | TensorPowerBlockGenerators・LeftBlock・BlockPermutations・FirstCrossing・FirstCrossingAction |
| Monoidal/TensorPower/FinBijection | PowerBijectionFunctor・PowerBijectionAppend |
| Monoidal/Action | ActionProductComparison・TensorActionTransport |
| Monoidal/Braided | BraidingPreservation・InternalHomExchange |
| Enriched/RepresentedMapping | Mapping{Adjunction,ParametrizedAdjunction,UnitLaws,Associativity,ArrowComposition,Whiskering}・RepresentedMappingEnrichment・RepresentedHomFunctor（今は Monoidal/ にあるが中身は豊穣圏） |
| Enriched/Transport | TransportOrdinaryEnrichment・TransportEnrichmentComparisons・LaxPointHom・ReverseComposition |
| Enriched/Simplicial | SimplicialHomLaws |
| Enriched/TensorCotensor | TensorCotensor・TensorUnit・EnrichedRepresentability |
| Adjunction/Comparison | ActionComparisonAdjunction・ActionUnitAdjunction・ActionComparisonNaturality・AdjunctionCompositeNaturality・HomEquivNaturality（モノイダル構造を使わない） |
| Quiver/FreePathComonad | FreePathComonad・PathObjectTransport |
| Quiver/PathMap | PathIntersections |
| Simplex/Prefix | Prefix・PrefixInterval |
| Simplex/GenRelEquivalence | PresentationDegeneracies・PresentationFaces・PresentationEquivalence（約 470 行） |
| Under | LiftingProperties/Under・MorphismProperty/UnderFactorization |
| Limits | Limits/InitialColimits・Limits/SequentialExtension・LiftingProperties/ParametrizedGeneration・Groupoid/ThinComponents |

### 3.3 Mathlib との重なり（固定版 2026-10-07 と最新版 2026-10-28 で差なし）

- `QuiverPaths.natTransOfEdges`（Quiver/PathNatTrans）= `Paths.liftNatTrans`（確度高）。
- `functor_ext_edges`・`prefunctor_hext`（Quiver/PathFunctorExt）= `Paths.ext_functor`（HEq の代わりに eqToHom、確度高）。
- Quiver/FreePathComonad の `comonad` ≈ `Quiv.adj.toComonad`（確度中〜高）、`mapPath` ≈ `Prefunctor.mapPath`（確度中）。
- `Simplex/Naturality.property` = `MorphismProperty.naturalityProperty`、証明は `SimplexCategory.morphismProperty_eq_top`（確度高）。
- `ActionComparisonAdjunction.rightIso`・`ActionUnitAdjunction.rightUnitIso` は `(a.ofNatIsoLeft e).rightAdjointUniq b`（確度高）。
- 豊穣化の作用は `MonoidalRightAction`、Transport* は `TransportEnrichment`・`enrichedOrdinaryCategory` と重なる見込み（確度中）。
- Mathlib にない（提出候補）：`SimplexCategoryGenRel ≌ SimplexCategory`（Mathlib に明示の TODO。最有力）、可換モノイド対象上の `Mod` の自由加群・
  極限・balanced tensor・対称モノイダル閉構造、Under 版の持ち上げ性質・分解、細い亜群と成分の同値、テンソル冪への置換群の作用。

### 3.4 その他

- 未使用の宣言：Enriched/TensorCotensor の自然性 5 つと `cotensor_triangle`、BalancedTensor 系の `_hom`・`_inv` 約 15 など（論文の層の計画
  §1.3.4 に一覧）。ファイルの中だけで使う約 120 の名前は private に。
- 104 本のうち 55 本が `backward.isDefEq.respectTransparency false` を設定。名前空間をファイル名から付けたもの（`SerrePositivity.HomEquivNaturality` など）に
  一般的な名前が入っている。`def …Law : Prop` で等式を包む書き方が多い。
- LiftingProperties/Under・UnderFactorization は Mathlib の名前空間に直接置いている。Mathlib を上げると衝突しうる（論文の層の計画 H に記録済み。
  この整理の間は Mathlib を上げない、ユーザー決定）。
- NerveHomotopy と NerveHomotopyUniverse はほぼ同じ（後者は `ULift` で宇宙を独立にしたもの）。NerveSimplexEndpoint と NerveSimplexStart は双対。

## 4. 論文の層の側の扱い

- 論文の層の計画の段階 0（殻と死んだファイルの一掃）からは、§1 のファイル（CategoryTheory の下位ディレクトリ・Nerve まわり・トップ階層の殻 7 本・
  Spectra の殻 4 本）を除いた。こちらでは触らない。
- CategoryTheory のトップ階層の残り（Karoubi・三角圏・t 構造・Euler・K₀ など）は論文の層の側で整理する。それらのファイルは §1 のファイルを import
  しない見込みだが、作業の前に互いに確かめる。
- 詳細の正本：`formalization-plans/refactor-plan.md` 第 1 章 §1.3（今後こちらでは更新しない。以後の正本はそちらの計画）。

## 5. 追加の伝達：HomologicalAlgebra/ComplexLimits/ の 3 本（2026-10-30）

ユーザーの決定により、次の 3 本も ∞ 基盤の側へ渡す。論文の層の側では触らない。

| ファイル | 行 | import | importer |
| --- | --- | --- | --- |
| HomologicalAlgebra/ComplexLimits/ExtendTruncationHom | 53 | `KST.LocalizingInvariants.CochainConnectiveLift`・Mathlib `Algebra.Homology.Embedding.Extend` | 下の 2 本、`EInfinity/ComplexLimits/ExtendTruncationHom` |
| HomologicalAlgebra/ComplexLimits/ExtendTruncationHomNaturality | 45 | 上の 1 本 | 下の 1 本、`EInfinity/ComplexLimits/ExtendTruncationHomNaturality` |
| HomologicalAlgebra/ComplexLimits/TruncationInclusionNaturality | 61 | 上の 1 本 | `EInfinity/ComplexLimits/TruncationInclusionNaturality`、`InfinityCategories/Derived/CoherentBar/Compact/PinchedCohomologyNaturality` |

- 名前空間は `SerrePositivity.EInfinity.ComplexLimits`。KST を import しているので、HomologicalAlgebra に置くと層が逆転する
  （論文の層の HomologicalAlgebra は ∞ 基盤より下）。
- `EInfinity/ComplexLimits/{ExtendTruncationHom, ExtendTruncationHomNaturality, TruncationInclusionNaturality}` は同名の再エクスポートの殻
  （commit fcc305646 で作られた互換ファイル）。実体を EInfinity/ComplexLimits/ へ移して殻と置き換えるのが自然。
- 論文の層の側（BhattScholze・CLMST・Paper ほか）は 3 本を import しない。`scripts/audit/shared.lean` が import しているので、移したら
  `python3 scripts/make_area_audits.py` で再生成する。

## 6. 追加の伝達：GroupTheory/Coxeter/ と Inputs/Homotopy/（2026-10-30）

ユーザーの決定により、次も ∞ 基盤の側へ渡す。論文の層の側では触らない。どちらも利用者は ∞ 基盤の側だけ。
（CategoryTheory/ArrowFactorization・ArrowFactorizationCategory・ArrowFactorizationTransport も ∞ 基盤の側へ渡す。こちらはユーザーが直接伝える。）

### 6.1 GroupTheory/Coxeter/（TypeA 955 行・FirstToLast 90・PermutationInduction 28・InvolutionRelations 37）

- 中身：A_n 型 Coxeter 群 ≅ Sₙ₊₁（`typeAHom`・`typeAEquivPerm`、挿入ソートの標準形による単射性）、隣接互換による置換の帰納法
  `permutation_induction_right`、`shiftPerm`・`firstToLastPerm`（= `(finRotate _).symm`）、対合の関係式 `involution_pair_cube`・`_square`。
  ArxivFormalization（commit 761bc6bc…）から移植（Coxeter/README.md）。
- 利用者：CategoryTheory/Monoidal（PermutationAction・TensorPowerBlockPermutations・TensorPowerFirstCrossingAction）、EInfinity/Operad/*・
  EInfinity/IntervalCuts/*、Spectra/SymmetricSequence/*。Paper・CLMST・BhattScholze・LengthAlgebra・IntersectionMultiplicity は使わない。
  refactoring-infinity-r2.md の R67 が Monoidal の利用者の再分類を計画済み。
- Mathlib との重なり（固定版・最新版で同じ）：
  - `permutation_induction_right` は `Equiv.Perm.mclosure_swap_castSucc_succ`（Perm/Sign.lean）と `Submonoid.induction_of_closure_eq_top_right`
    から出る（確度高）。TypeA の 955 行が不要になりうる（`typeAEquivPerm` を使うのが PermutationAction だけなら）。
  - `adjacentTransposition` は `swap i.castSucc i.succ`。`shiftPerm`・`firstToLastPerm` は `Equiv.Perm.decomposeFin`・`finRotate`・`Fin.cycleRange` と重なる（確度中）。
  - A_n ≅ Sₙ₊₁ は Mathlib にない（`CoxeterMatrix.A`・`CoxeterSystem` はあるが対称群との同型はない、確度高）。残すなら提出候補。
- ファイルの外で使われていない：`typeAHom_injective`・`typeAHom_surjective`・`typeANormalForm*`、TypeA の `bubble*`・`perm*`・`groupLift`。
- GroupTheory/ConjugateSum は論文の層のまま（CategoryTheory/EulerComparison が使う）。こちらで改名して EulerComparison へ吸収する予定なので、
  Coxeter/ だけが GroupTheory/ に残る。置き場所はそちらで決めてほしい。

### 6.2 Inputs/Homotopy/（KanQuillen・ResolutionHom・SimplicialLevel）

- KanQuillen：`kanQuillen_model_exists`（Hovey Thm 3.6.5、`sorry`。`make_area_audits.py` が許している引用）と `kanQuillenModel`・射影の補題 3 つ。
- ResolutionHom・SimplicialLevel：KanQuillen の適用（`sorry` なし）。scripts の check（check_kan_quillen_resolution_hom・check_model_replacement・
  check_kan_quillen_level）だけが import。`resolutionHom_source_geometricWeakEquivalence` はどこからも使われない。
- 主定理の閉包の外（scripts/refactor/verify.log で確認済み）。KST の経路の計画では γ-B を採れば HT-KQ は不要。
- 論文の層の Inputs/ には Descent（Thm 3.1）だけを残す。Inputs/Homotopy/ は ∞ 基盤の引用の置き場へ移すのが自然
  （`make_area_audits.py` の許可リストの更新も一緒に）。Inputs/DifferentialGraded/（README だけ、採用 0 件）も dg の側。

## 7. 追加の伝達：CategoryTheory のトップ階層のうち ∞ 基盤の側だけが使う 12 本（2026-10-30）

CategoryTheory のトップ階層の残りを、import の逆向きの閉包で分類した結果、次の 12 本は利用者が ∞ 基盤の側（Spectra・HomotopicalAlgebra・
EInfinity・KST と CategoryTheory の下位ディレクトリ）だけだった。ユーザーの決定により ∞ 基盤の側へ渡す。論文の層の側では触らない。
（論文の層から届くように見えた経路は Inputs/Homotopy（§6 で渡したもの）経由だけ。）

| ファイル | 行 | importer |
| --- | --- | --- |
| CategoryTheory/AdjunctionHomLaws | 147 | Monoidal/AdjunctionCompositeNaturality・Monoidal/MappingUnitLaws・Spectra/SymmetricSpectrum/MappingSpace |
| CategoryTheory/CommaIdentities | 56 | HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/IndexReedy |
| CategoryTheory/FiniteBijection | 113 | FiniteBijectionAction・FiniteBijectionSum・Spectra/SymmetricSequence/FiniteBijection |
| CategoryTheory/FiniteBijectionAction | 68 | Monoidal/PowerBijectionFunctor |
| CategoryTheory/FiniteBijectionInduction | 58 | Spectra/ModelCategory/FreeLevelCofibrations |
| CategoryTheory/FiniteBijectionShift | 20 | FiniteBijectionInduction・Spectra/SymmetricSequence/FreeInduction |
| CategoryTheory/FiniteBijectionSum | 47 | FiniteBijectionShift・Monoidal/PowerBijectionAppend・Spectra/SymmetricSequence/DisjointUnion |
| CategoryTheory/FiniteBlockEquiv | 56 | FiniteBijectionSum・Monoidal/TensorPowerBlockPermutations・EInfinity/Operad/SlotPermutations |
| CategoryTheory/FunctorTransport | 66 | Spectra/General/PointwiseTensor・Spectra/SymmetricSequence/PointwiseTensorModule・Spectra/SymmetricSpectrum/CotensorFunctor |
| CategoryTheory/ParametrizedAdjunctionTransport | 72 | HomotopicalAlgebra/Localization/Monoidal・Spectra/General/{ParametrizedCotensor,ParametrizedMapping}・Spectra/ModelCategory/{GeneralLevelTensor,SimplicialLevelTensor} |
| CategoryTheory/PointwiseAdjunction | 46 | HomotopicalAlgebra/Diagram/ProjectiveBifunctor |
| CategoryTheory/RelativeArrow | 150 | HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/{BoundaryDiagram,RelativeArrow} |

これで §4 で確かめた互いの import（こちら → ∞ 側 1 件、∞ 側 → こちら 5 件）はすべて ∞ 基盤の側の中の依存になる
（FiniteBijectionInduction → Groupoid/ThinComponents、Monoidal/* → AdjunctionHomLaws・FiniteBijectionAction・FiniteBlockEquiv・FiniteBijectionSum）。

調査の記録（論文の層の計画 §1.2.2・§1.2.4、そちらへの申し送り）：
- `FunctorTransport.transport`・`iso`・`transport_obj`・`iso_hom_app` は Mathlib の `Functor.copyObj`・`isoCopyObj`（NatIso）と同じ（確度高）。ファイルごと置き換えられる。
- AdjunctionHomLaws は `*Law : Prop` とその補題がどれも `Adjunction.homEquiv_naturality_left/right`・`Equiv.left_inv/right_inv`・`homEquiv_unit` の言い直し、
  `comparisonHomEquiv` ≈ `a.homEquiv … |>.trans (e.homCongr …)`（確度高）。未使用：`curryEvaluationLaw`・`evaluationEqualityLaw`・`evaluation_injective`・
  `comparisonHomEquiv_symm_apply`。
- `RelativeArrow`（自然変換の相対 pushout・pullback の射）は Mathlib の `Functor.PushoutObjObj`・`PullbackObjObj` で書ける可能性（確度低〜中）。
- `ParametrizedAdjunctionTransport`（`restrict`・`composeSecond`・`left`・`right`）は Mathlib の `ParametrizedAdjunction` の拡張で、上流にない。提出候補。
- FiniteBijection は `Core FintypeCat.Skeleton` の薄い包み。FiniteBlockEquiv は `Fin` の同値。
- 未使用：`FiniteBijectionInduction.addRight_faithful`（instance）。

## 8. 追加の伝達：区切り 1-1 で main のモジュール名が変わった（2026-10-30）

main に区切り 1-1 が入った（ca2fffe4d・25d50e9e8）。∞ 基盤・DG・KST の worktree で main を取り込むとき、次の import 行を書き換える。
main 側の ∞・DG・KST のファイル（DG 7 本・KST 1 本・InfinityCategories/Derived/Localization）は書き換え済み。worktree で新しく足したファイルだけが対象になる。

- CategoryTheory のトップ階層 68 本を 20 本にまとめた（下の表、`SerrePositivity.` は省略）。宣言名は変えていない。
  ただし `GroupTheory.ConjugateSum` は `CategoryTheory.Euler` に入り、`conjSum_eq` → `orbitSum_eq_of_descent`、
  `conjSum_eq_of_base_formula` → `orbitSum_eq_of_base_formula` に改名した。`triangle_isIso_of_components` は削除し、Mathlib の
  `Triangle.isIso_of_isIsos` を使う。`smul_mul_self_id_eq_zero`・`pow_smul_id_eq_zero_of_le` は HomologicalAlgebra/NullHomotopy から
  新しい `CategoryTheory/LinearScalar` に移した。
- `IsModuleSTorsion` を廃止した。Mathlib の `Module.IsTorsion' M S` を使い、`IsModuleSTorsion.iff_localized_zero` →
  `isTorsion'_iff_subsingleton_localizedModule`、`.iff_tensor_zero` → `isTorsion'_iff_subsingleton_tensor`、`.of_exact` → `isTorsion'_of_exact`、
  要素ごとの形は `isTorsion'_iff_forall`（いずれも `CommutativeAlgebra/Localization/PowerTorsion`）。
- CommutativeAlgebra の他の改名の全表は ca2fffe4d のコミットメッセージにある。

| 旧 | 新 |
| --- | --- |
| `CategoryTheory.AdditiveLength` | `CategoryTheory.Abelian.SerreLength` |
| `CategoryTheory.BoundedHomotopyGeneration` | `CategoryTheory.BoundedHomotopy` |
| `CategoryTheory.BoundedTStructureGeneration` | `CategoryTheory.TStructure.Bounded` |
| `CategoryTheory.BoundedTStructureIdempotent` | `CategoryTheory.TStructure.Bounded` |
| `CategoryTheory.CommShiftOfPrecomp` | `CategoryTheory.Triangulated.VerdierLift` |
| `CategoryTheory.ConeLengthBinomial` | `CategoryTheory.IteratedCone` |
| `CategoryTheory.ConeLengthCancellation` | `CategoryTheory.IteratedCone` |
| `CategoryTheory.CubicConjugation` | `CategoryTheory.Triangulated.Idempotent` |
| `CategoryTheory.DerivedPure` | `CategoryTheory.Derived` |
| `CategoryTheory.EulerComparison` | `CategoryTheory.Euler` |
| `CategoryTheory.ExactImageSequence` | `CategoryTheory.Abelian.ShortComplex` |
| `CategoryTheory.ExactRetract` | `CategoryTheory.Abelian.ShortComplex` |
| `CategoryTheory.ExactSequenceEuler` | `CategoryTheory.Euler` |
| `CategoryTheory.FamilyTStructure` | `CategoryTheory.TStructure.Family` |
| `CategoryTheory.FamilyTriangulatedImage` | `CategoryTheory.TStructure.Family` |
| `CategoryTheory.FiniteSupportBounds` | `CategoryTheory.AlternatingSum` |
| `CategoryTheory.FullSubcategoryTriangle` | `CategoryTheory.HomotopyProperty` |
| `CategoryTheory.HomologicalConeLength` | `CategoryTheory.IteratedCone` |
| `CategoryTheory.HomologicalEuler` | `CategoryTheory.Euler` |
| `CategoryTheory.HomologicalKernelTStructure` | `CategoryTheory.TStructure.Localization` |
| `CategoryTheory.HomologicalLocalization` | `CategoryTheory.Triangulated.VerdierLift` |
| `CategoryTheory.HomotopyConeRepresentative` | `CategoryTheory.HomotopyProperty` |
| `CategoryTheory.KaroubiExtensionOne` | `CategoryTheory.Karoubi.Triangulated` |
| `CategoryTheory.KaroubiFullyFaithful` | `CategoryTheory.Karoubi.Basic` |
| `CategoryTheory.KaroubiHomological` | `CategoryTheory.Karoubi.Triangulated` |
| `CategoryTheory.KaroubiImage` | `CategoryTheory.Karoubi.Basic` |
| `CategoryTheory.KaroubiLinear` | `CategoryTheory.Karoubi.Basic` |
| `CategoryTheory.KaroubiPretriangulated` | `CategoryTheory.Karoubi.Triangulated` |
| `CategoryTheory.KaroubiScalarSupport` | `CategoryTheory.ScalarSupport` |
| `CategoryTheory.KaroubiShift` | `CategoryTheory.Karoubi.Basic` |
| `CategoryTheory.KaroubiTriangulated` | `CategoryTheory.Karoubi.Triangulated` |
| `CategoryTheory.KaroubiTriangulatedFunctor` | `CategoryTheory.Karoubi.Triangulated` |
| `CategoryTheory.LocalizationTStructure` | `CategoryTheory.TStructure.Localization` |
| `CategoryTheory.OctahedronBlockRetract` | `CategoryTheory.Triangulated.Padding` |
| `CategoryTheory.OctahedronEssentialImage` | `CategoryTheory.Triangulated.Padding` |
| `CategoryTheory.OctahedronPadding` | `CategoryTheory.Triangulated.Padding` |
| `CategoryTheory.ScalarSupportEquivalence` | `CategoryTheory.ScalarSupport` |
| `CategoryTheory.ScalarSupportLocalization` | `CategoryTheory.ScalarSupport` |
| `CategoryTheory.ScalarSupportRadical` | `CategoryTheory.ScalarSupport` |
| `CategoryTheory.ScalarZeroCone` | `CategoryTheory.IteratedCone` |
| `CategoryTheory.SemilinearScalar` | `CategoryTheory.ScalarSupport` |
| `CategoryTheory.SerreDerivedQuotient` | `CategoryTheory.Derived` |
| `CategoryTheory.SerreLength` | `CategoryTheory.Abelian.SerreLength` |
| `CategoryTheory.SerreSubcategory` | `CategoryTheory.Abelian.SerreLength` |
| `CategoryTheory.ShortExactCokernel` | `CategoryTheory.Abelian.ShortComplex` |
| `CategoryTheory.SubcategoryLinear` | `CategoryTheory.Triangulated.VerdierLift` |
| `CategoryTheory.TExactKernelQuotient` | `CategoryTheory.TStructure.Localization` |
| `CategoryTheory.TExactTruncation` | `CategoryTheory.TStructure.Basic` |
| `CategoryTheory.TStructureHeart` | `CategoryTheory.TStructure.Basic` |
| `CategoryTheory.TStructureRetracts` | `CategoryTheory.TStructure.Basic` |
| `CategoryTheory.ThreeComponentMaps` | `CategoryTheory.Triangulated.Idempotent` |
| `CategoryTheory.TriangleBiproduct` | `CategoryTheory.Triangulated.Padding` |
| `CategoryTheory.TriangleIdempotent` | `CategoryTheory.Triangulated.Idempotent` |
| `CategoryTheory.TriangleIdempotentCompletion` | `CategoryTheory.Triangulated.Idempotent` |
| `CategoryTheory.TrianglePadding` | `CategoryTheory.Triangulated.Padding` |
| `CategoryTheory.TriangulatedK0Shift` | `CategoryTheory.TriangulatedK0` |
| `CategoryTheory.TruncationTriangle` | `CategoryTheory.BoundedHomotopy` |
| `CategoryTheory.VerdierKaroubi` | `CategoryTheory.Triangulated.VerdierKaroubi` |
| `CategoryTheory.VerdierKaroubiLinear` | `CategoryTheory.Triangulated.VerdierKaroubi` |
| `CategoryTheory.VerdierLift` | `CategoryTheory.Triangulated.VerdierLift` |
| `CategoryTheory.VerdierTStructure` | `CategoryTheory.TStructure.Localization` |
| `GroupTheory.ConjugateSum` | `CategoryTheory.Euler` |
