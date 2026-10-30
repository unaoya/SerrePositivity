# CategoryTheory の整理計画（2026-10-30）

概要：`SerrePositivity/CategoryTheory/`（206 ファイル、約 17200 行。トップ階層 102、下位ディレクトリ 104：Monoidal/ 67・Presentation/ 15・
Quiver/ 7・Simplex/ 6・Enriched/ 3 ほか）について、ファイルの統合、死んだファイル・未使用の削除、Mathlib への置き換え、置き場所と層の修正、
提出候補をまとめる。調査（2026-10-30、読むだけ）の結果を元にした計画で、実作業はまだ行っていない。
方針：作業の決まりは [commutative-algebra-refactor-plan.md](commutative-algebra-refactor-plan.md) の §2 と同じ。下位ディレクトリ（§3）を使うのは
∞ 圏の基盤の側（Spectra・HomotopicalAlgebra・EInfinity・KST）だけなので、[infinity-foundation-plan.md](infinity-foundation-plan.md) の作業
（Codex の指示書 IF-WN-k）と時期・範囲を合わせる。
規約：Mathlib の確認は固定版（2026-10-07）と最新版（2026-10-28）の両方で行い、調べた概念では差がなかった。`sorry`・`axiom`・外せない仮定
（`[ModelCategory SSet]` など）・`maxHeartbeats` の引き上げはない。
使われ方：作業を再開するときの手順書。

## 1. 外への影響

- BhattScholze が使うのは `ExactDerivedTStructure` の 1 本だけ（BS/Almost/PerfectoidAlmost が `derived_isZero_iff_homology` を使う）。
  名前と、その import の閉包を残す。CLMST は CategoryTheory を import しない。
- トップ階層（§2）の利用者は論文の層全般（Asymptotic・PerfectComplex・KTheory・LengthAlgebra・Paper）。
- 下位ディレクトリ（§3）の利用者は Spectra・HomotopicalAlgebra（主に `HomotopicalAlgebra/GeneralTools` の再エクスポート経由）・EInfinity・KST。

## 2. トップ階層（102 → 約 30 ファイル）

### 2.1 統合

| 新しいファイル | 元のファイル |
| --- | --- |
| Karoubi/Basic | KaroubiLinear・KaroubiShift・KaroubiFullyFaithful・KaroubiImage |
| Karoubi/Triangulated | KaroubiPretriangulated・KaroubiTriangulated・KaroubiTriangulatedFunctor・KaroubiExtensionOne・KaroubiHomological（Balmer–Schlichting） |
| Triangulated/Idempotent | TriangleIdempotent・TriangleIdempotentCompletion・CubicConjugation・ThreeComponentMaps |
| Triangulated/Padding | TriangleBiproduct・TrianglePadding・OctahedronBlockRetract・OctahedronPadding・OctahedronEssentialImage |
| Triangulated/VerdierLift | CommShiftOfPrecomp・VerdierLift・HomologicalLocalization・SubcategoryLinear |
| Triangulated/VerdierKaroubi | VerdierKaroubi・VerdierKaroubiLinear |
| TStructure/Basic | TStructureHeart・TStructureRetracts・TExactTruncation |
| TStructure/Bounded | BoundedTStructureIdempotent・BoundedTStructureGeneration |
| TStructure/Localization | LocalizationTStructure・VerdierTStructure・TExactKernelQuotient・HomologicalKernelTStructure |
| TStructure/Family | FamilyTStructure・FamilyTriangulatedImage |
| Derived | DerivedPure・ExactDerivedTStructure・SerreDerivedQuotient（ExactDerivedTStructure は BS が使うので、閉包を重くしないよう別に残す案も） |
| Abelian/SerreLength | SerreSubcategory・SerreLength・AdditiveLength |
| Abelian/ShortComplex | ExactImageSequence・ExactRetract・ShortExactCokernel |
| TriangulatedK0 | TriangulatedK0・TriangulatedK0Shift |
| Euler | HomologicalEuler・EulerComparison・ExactSequenceEuler |
| IteratedCone | HomologicalConeLength・IteratedCone・ScalarZeroCone |
| ScalarSupport（2 本） | ScalarSupport*・SemilinearScalar・KaroubiScalarSupport |
| BoundedHomotopy | BoundedHomotopy・BoundedHomotopyGeneration・TruncationTriangle |
| HomotopyProperty | HomotopyProperty・HomotopyConeRepresentative・FullSubcategoryTriangle |
| Nerve | NerveHomotopy・NerveHomotopyUniverse（§2.3）・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・NerveVertices |
| Simplex/Chains | SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp |
| FiniteBijection（2 本） | FiniteBijection*（Spectra・Monoidal・EInfinity だけが使う） |
| Adjunction | ParametrizedAdjunctionTransport・PointwiseAdjunction（AdjunctionHomLaws は削除、§2.2） |
| Arrow | RelativeArrow・CommaIdentities（ArrowFactorization* は Mathlib へ、§2.2） |

- 圏論でないものを外へ：AlternatingSum（ℤ → ℝ の finsum）・FiniteSupportBounds（`Function.HasFiniteSupport` の補題 1 つ）・ConeLengthBinomial・
  ConeLengthCancellation（ℤ → ℝ の二項係数の演算子の計算）→ 一般の補題のファイル（Mathlib 形式）へ。WellFoundedHistory（順序・論理、
  唯一の利用者は CA/ResidueFieldExtension）→ そちらへ。FiniteBlockEquiv（`Fin` の同値）→ FiniteBijection の近く。
- 層の逆転：
  - ScalarSupport が HomologicalAlgebra/NullHomotopy を import しているのは一般の線形圏の補題 2 つ（`smul_mul_self_id_eq_zero`・
    `pow_smul_id_eq_zero_of_le`）のため。その 2 つを CategoryTheory（SemilinearScalar）へ下ろす。
  - TruncationTriangle が HomologicalAlgebra/StupidTruncation を import（StupidTruncation の Mathlib 化は保留中、HA 計画 §2.2）。
  - EulerComparison が GroupTheory/ConjugateSum を import。
  - NerveVertices が HomotopicalAlgebra/Simplicial/VertexTuples を、NerveSimplexFirstFunctor が HomotopicalAlgebra/Simplicial/SimplexNerveAugmentation
    を import し、後者は CategoryTheory/SimplexChainVertices を import する（ディレクトリをまたいだ循環に近い）。∞ 基盤の計画と合わせて、
    Nerve*・Simplex/Chains を HomotopicalAlgebra/Simplicial 側へ移すか、逆に VertexTuples を下ろすかを決める。
  - 再エクスポートの殻 7 本が HomotopicalAlgebra/Rectification を import（§2.4 で削除）。

### 2.2 Mathlib との重なり（確度高のもの）

- `FunctorTransport.transport`・`iso`・`transport_obj`・`iso_hom_app` = `Functor.copyObj`・`isoCopyObj`（NatIso）。ファイルごと削除。
- ArrowFactorization・ArrowFactorizationCategory（`source_isInitial`・`target_isTerminal`）≈ `CategoryTheory.Factorisation`（`initial`・`terminal`・
  `IsInitial_initial`・`IsTerminal_terminal`）。宇宙の扱い（Mathlib は hom の宇宙が `max u v`）に注意して置き換える。
- `triangle_isIso_of_components` = `Triangle.isIso_of_isIsos`。
- `triangleBiproduct_distinguished` は `productTriangle_distinguished` の薄い系として書き直す（確度中〜高）。
- AdjunctionHomLaws：`*Law : Prop` とその補題はどれも `Adjunction.homEquiv_naturality_left/right`・`Equiv.left_inv/right_inv`・`homEquiv_unit`
  の言い直し。`comparisonHomEquiv` ≈ `a.homEquiv … |>.trans (e.homCongr …)`。ファイルごと不要。
- HomologicalLocalization は `Functor.mem_homologicalKernel_trW_iff` の 5 行の包み、ShortExactCokernel は
  `(cokernelIsCokernel _).coconePointUniqueUpToIso hS.gIsCokernel`（`Adams.` の別名つき）。インライン化。
- VerdierLift は `Localization.lift`・`commShiftOfLocalization`・`Functor.IsTriangulated` の補題で大部分が作れる（確度中）。
  `commShiftOfPrecomp`（前合成の版）は Mathlib にない（`Functor.CommShift.ofComp` は後合成の版）。
- Mathlib にないもの：三角圏の Karoubi 完備化（シフト・pretriangulated・triangulated）、Karoubi の `Linear`、ハートのインスタンス（abelian・
  `ContainsZero`・有限積）、t 構造の retract での安定性、局所化への t 構造、三角圏の K₀、有界ホモトピー圏、自然変換から脈体のホモトピー、
  `Exact.of_retract`、`P.isoModSerre.Localization` の Abelian インスタンス。

### 2.3 一本化

- NerveHomotopy と NerveHomotopyUniverse はほぼ同じ（後者は `ULift` で宇宙を独立にしたもの）。一般の版から同じ宇宙の版を導く。
- NerveSimplexEndpoint と NerveSimplexStart は双対（`tail` と `initialSegment`）。一つの構成に。
- `localizationTStructure` と `verdierTStructure`（後者は前者の特殊化）。`*_isIdempotentComplete`・`*_has_representative`・`*KaroubiEquivalence`
  が 4 回（BoundedTStructureIdempotent・LocalizationTStructure・VerdierTStructure・TExactKernelQuotient/SerreDerivedQuotient）。
- Asymptotic・LengthAlgebra・Paper の `*EulerK0 : TriangulatedK0 … →+ ℝ` は `homologicalEulerK0`・`TriangulatedK0.lift` の型の繰り返し
  （[asymptotic-refactor-plan.md](asymptotic-refactor-plan.md) §5）。
- `DerivedPure.derivedPureHomologyIso` は `Classical.choice` でデータを作っている。HA の `normalizedPureHomologyIso`（同じく `.choose`）と
  一本化し、明示的な構成にする（HA 計画 §3.5）。

### 2.4 死んだファイル・未使用

- 死んだファイル：再エクスポートの殻 7 本（AnchoredChain*・ArrowContext・LabelledChain・SimplexChainParameter。importer は
  `scripts/audit/shared.lean`・`scripts/audit_homotopical_foundations.lean` だけ）、EulerTheory（ルートと scripts だけが import する集約ファイル）。
- 未使用の宣言（instance を除く）：`additiveLength_le_of_retract`、AdjunctionHomLaws の 4 つ、`pre_post_transport`、`essSurj_of_bounded_of_heart`、
  `boundedSubcategory_isIdempotentComplete`・`boundedTStructureKaroubiEquivalence`・`karoubi_bounded_has_representative`、
  `coneLength_binomial_homological`、FunctorTransport の 3 つ、`homologicalEuler_natIso`・`homologicalEulerK0_unique`・`homologicalEulerK0_pullback`、
  `iteratedZeroCone_iso`・`iteratedZeroCone_length_lower_bound`、`karoubi_smul_f`（simp）、KaroubiShift の simp 補題、
  `exists_tExact_localizationTStructure_iff`、`serreDerivedQuotientKaroubi_has_bounded_complex`、`serreQuotientLength_obj`（simp）、
  `heart_isIdempotentComplete`、`karoubi_pure_has_representative`、`completedKaroubiFirstToLast_isEquivalence`、`verdierTStructure_le/_ge`・
  `verdierKaroubiEquivalence`。simp の補題は消す前にビルドで確かめる。

### 2.5 その他

- 一般的すぎる名前が裸の `SerrePositivity` 名前空間に多い（`conjugate_cube`・`conjugate_projection`・`section_sum0/1/2`・
  `three_components_rotation`・`idempotent_cubic`・`biprodDescComp`・`heart_containsZero`・`familyMap`・`familyFunctor`・
  `finiteSupport_of_bounded_zero`・`alternatingFinsum_*`・`pure_mem_of_heart`・`bounded_le_of_heart`・`localization_hom_eq_zero` など）。
  `SerrePositivity.Triangulated`・`.TStructure`・`.Karoubi` に入れる。
- `def …Law : Prop` で等式を包む書き方（AdjunctionHomLaws、§3 の Monoidal の多く）はやめ、補題の主張に直接書く。
- VerdierKaroubi の `synthInstance.maxSize 512`、約 30 ファイルの `backward.*` の移行用オプションは、統合のときに外せるか試す。

### 2.6 提出候補（価値の高い順）

三角圏の Karoubi 完備化（シフト・Linear・pretriangulated・triangulated、八面体は padding で）、ハートのインスタンス、t 構造の retract での安定性と
有界なら冪等完備、Verdier 局所化への t 構造、前合成についての `Functor.CommShift`、自然変換から脈体のホモトピー、`ShortComplex.Exact.of_retract`、
`P.isoModSerre.Localization` の Abelian、三角圏の K₀（`mk_shift`）、有界ホモトピー圏、`ParametrizedAdjunction.restrict`。

## 3. 下位ディレクトリ（104 → 約 35 ファイル。利用者は ∞ 基盤の側だけ）

### 3.1 死んだファイル

- Presentation/ の 15 本すべてと Quiver/WeightedPaths・WeightedPathMaps：各 24 行で、同名の `HomotopicalAlgebra/Rectification/CategoryTheory/…`
  を再エクスポートするだけ。importer なし、ルートにもない。参照は `scripts/homotopical_generalization_manifest.json` だけ。削除してマニフェストを直す。
- Spectra/SymmetricSequence の殻 4 本（TensorPowers・TensorPermutations・AdjacentTranspositions・AdjacentBraid、各 10 行で Monoidal/* を再エクスポート）。
  importer を張り替えて削除。

### 3.2 統合

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
| Simplex/Naturality | Naturality（§3.3 で中身の大半は Mathlib へ） |
| Under | LiftingProperties/Under・MorphismProperty/UnderFactorization |
| Limits | Limits/InitialColimits・Limits/SequentialExtension・LiftingProperties/ParametrizedGeneration・Groupoid/ThinComponents |

### 3.3 Mathlib との重なり

- `QuiverPaths.natTransOfEdges`（Quiver/PathNatTrans）= `Paths.liftNatTrans`（確度高、そのまま置き換え）。
- `functor_ext_edges`・`prefunctor_hext`（Quiver/PathFunctorExt）= `Paths.ext_functor`（HEq の代わりに eqToHom、確度高）。
- Quiver/FreePathComonad の `comonad` ≈ `Quiv.adj : Cat.free ⊣ Quiv.forget` の `.toComonad`（確度中〜高）。`mapPath` ≈ `Prefunctor.mapPath`（確度中）。
- `Simplex/Naturality.property` = `MorphismProperty.naturalityProperty`、証明は `SimplexCategory.morphismProperty_eq_top`（確度高、def は不要）。
- `rightIso`（ActionComparisonAdjunction）・`rightUnitIso`（ActionUnitAdjunction）は `(a.ofNatIsoLeft e).rightAdjointUniq b`（確度高、インライン化）。
- 豊穣化の作用 `H : V ⥤ D ⥤ D` と `a : H(P⊗Q) ≅ H Q ⋙ H P` は `MonoidalRightAction` で書き直せる見込み（確度中）。Transport* は
  `TransportEnrichment`・`enrichedOrdinaryCategory` と重なる（確度中）。
- Mathlib にないもの：`SimplexCategoryGenRel ≌ SimplexCategory`（Mathlib に明示の TODO）、可換モノイド対象上の `Mod` の自由加群・極限・余極限・
  balanced tensor・対称モノイダル閉構造（Mathlib の `Mod` は圏と `regular`・`forget`・`comap` だけ）、Under 版の持ち上げ性質・分解、
  細い亜群と成分の同値。Presentable・Day convolution は Mathlib（固定版）にあるが、ここでは使っていない（Presentation/ は語の表示の話）。

### 3.4 未使用

Enriched/TensorCotensor の自然性 5 つと `cotensor_triangle`、`unitMap_isIso`、SequentialExtension の `stage_zero`・`descend_zero`、
BalancedTensor 系の `_hom`・`_inv` の補題約 15、`freeHomIso_naturality_left`・`freeHomObj_action_formula`、`homBifunctor_map`、
ModuleTransport の `iso_inv`・`obj_action`、`comparison_inv_naturality`、`mapPath_singleton`、`ofFacesDegeneracies_app`、`standardδ_comp`・
`standardδ_nil`。ファイルの中だけで使われている約 120 の名前は private に。

### 3.5 その他

- 104 本のうち 55 本が `backward.isDefEq.respectTransparency false`（と `.types false`）を設定（Mod の一群と Quiver の全部）。外せるか試す。
- ファイル名の名前空間（`SerrePositivity.HomEquivNaturality`・`.ReverseComposition`・`.LaxPointHom` など）に一般的な名前（`derived`・`pre`・
  `parameter`・`identity`・`composition`・`points`・`left_action`・`map`）が入っている。Limits/InitialColimits は裸の `SerrePositivity` に宣言。
  LiftingProperties/Under・UnderFactorization は Mathlib の名前空間（`CategoryTheory.CommSq.HasLift.under` など）に直接置いている
  （提出の準備としてはよいが、Mathlib を上げたときに衝突しうる）。
- Quiver/・Simplex/ の docstring が同じ定型文（「分類A」「生成辺と空の道…」）の繰り返し。

### 3.6 提出候補（強い順）

1. `SimplexCategoryGenRel ≌ SimplexCategory` と P_δ の一意な標準形（Mathlib の TODO を埋める）。
2. 自由 `Mod` ⊣ forget、`Mod.forget` が極限・余極限を作る、可換 M についての `Mod C M` の対称モノイダル閉構造。
3. LiftingProperties/Under・MorphismProperty/UnderFactorization（Over 版の双対、小さく準備済み）。
4. Limits/InitialColimits、Groupoid/ThinComponents。
5. 対称モノイダル圏のテンソル冪への `Equiv.Perm (Fin n)` の作用。
6. `map_braiding_tensor_left`（BraidingPreservation）。

## 4. 順序と決定待ち

1. 死んだファイル（§2.4 の 8 本、§3.1 の 21 本）と確度高の Mathlib への置き換えを先に（BS/CLMST の波及なし。Presentation の殻はマニフェストだけ）。
2. トップ階層の統合（§2.1）。BS が使う ExactDerivedTStructure の閉包は変えない。
3. 下位ディレクトリの統合（§3.2）は ∞ 基盤の作業と時期を合わせる。

決定待ち：Nerve*・Simplex/Chains と HomotopicalAlgebra/Simplicial の境界（どちらへ寄せるか）。下位ディレクトリの整理を ∞ 基盤の Codex の
指示書に含めるか、こちらで行うか。
