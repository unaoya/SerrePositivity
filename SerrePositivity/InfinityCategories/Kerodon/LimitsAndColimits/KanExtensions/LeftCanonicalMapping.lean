module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionMappingPair
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalRestrictionHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion

/-!
概要：標準左 Kan 関手から出る元の関手制限の写像空間の同値。
方針：標準局所余極限を全パラメータの定値族へ移し、指定 pinched 比較の判定を使う。
規約：相手の関手には Kan 条件を要求しない。
使われ方：元の左 Kan 関手の全部分圏からの制限の充満忠実性。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標準左 Kan 関手から出る元の制限の右 pinched 写像はホモトピー同値。
方針：定値パラメータ族の Hom 全単射を転置して全パラメータの判定へ渡す。
規約：δ の単射性は不要であり、G の局所普遍性も不要。
使われ方：元の Kan 関手全体からの制限の写像空間の主定理。 -/
lemma kanLeftCanonical_pinchedHomMap_equivalence {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre δ).app D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precomposition_pinchedHomMap_equivalence_of_constantFamily δ F G
    (fun A ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHomMap_constantFamily_bijective δ F hF
      (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A D))

/-- 概要：単射による制限は標準左 Kan 関手で始まる境界を充填する。
方針：全ての相手への指定 pinched 比較の同値を相対始対象の境界判定へ渡す。
規約：単射性は制限の inner fibration 性のためだけに使う。
使われ方：元の Kan 関手全体の制限からの境界固定の延長。 -/
lemma kanLeftCanonical_pre_initialBoundary {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting ((pre δ).app D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_iff_initialBoundary ((pre δ).app D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)).1
  intro y
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).surjective y
  exact kanLeftCanonical_pinchedHomMap_equivalence δ F hF G

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.1.5.6" (partial := component) "仮定：P(S) から小余完備な準圏への小余極限保存関手二つ（Lean が強い：S は準圏）。結論：同じ米田写像への制限は、この二関手間の全写像空間で同値となり、指定 Funᴸ 上で充満忠実である（結論の一部に一致。制限の本質的全射性を含む全関手準圏の同値は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_equivalence
attribute [cite HTT "5.3.6.4" (partial := component) "仮定：小準圏 C と小余完備 D、P(C)→D の小余極限保存関手（Lean が強い：C は任意の単体集合でなく準圏）。結論：同じ米田制限が保存関手間の全写像空間で同値となる（普遍性の充満忠実性と一致）。全制限射の本質的全射性を含む同値までの証明はない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_equivalence
attribute [cite HTT "5.3.6.6" (partial := component) "仮定：小準圏 C、K 空、K′ は全小形状（Lean が強い：任意の小単体集合 C ではない）。結論：P(C) の同じ制限の全写像空間での同値、すなわち普遍性の充満忠実性（一致する成分）。抽象的 PK′K との比較同値を構成したとは数えない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_equivalence
