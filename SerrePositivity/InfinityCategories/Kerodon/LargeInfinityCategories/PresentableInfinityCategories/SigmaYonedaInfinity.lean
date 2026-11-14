module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.DiscreteCoherentSpaceProducts
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.LiftedConePointedRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityFullyFaithful

/-!
概要：元の Yoneda ∞ 関手を P_Σ(C) へ因子化する。
方針：元の表現可能前層の全錐の一点切断判定と、元の離散図式の極限の存在を使う。
規約：元の Yoneda 写像を包含後に厳密に回収し、別の Hom 前層に置き換えない。
使われ方：HTT 5.5.8.10、P_Σ の sifted 余極限による生成と普遍性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の Yoneda 前層は、元の有限離散極限錐を全錐ごと保存する。 -/
lemma representablePresheafInfinity_preservesFiniteProducts
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PreservesFiniteProductsFromSmallSource (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) := by
  intro J _ D c hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.spaceCone_isLimit_of_pointRestriction_of_hasLimit
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hasLimit_discreteCoherentSpaceDiagram _
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableNativeConePointedRestriction_isQCatEquivalence c hc y

/-- 元の Yoneda 前層は、元の P(C) 内で P_Σ の対象条件を満たす。 -/
lemma representablePresheafInfinity_isSigmaPresheaf
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSigmaPresheaf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isSigmaPresheaf_object_iff _).mpr (representablePresheafInfinity_preservesFiniteProducts y)

/-- 元の Yoneda ∞ 関手を、元の対象と全高次の射を保って P_Σ(C) へ因子化。 -/
def sigmaYonedaInfinityMap (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (fun a ↦ by
    obtain ⟨a⟩ := a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex]
    exact representablePresheafInfinity_isSigmaPresheaf a)

/-- P_Σ への因子化を包含すると、元の Yoneda ∞ 関手を厳密に回収する。 -/
lemma sigmaYonedaInfinityMap_inclusion (C : SSet.{u}) [Quasicategory C] :
    sigmaYonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityLift_inclusion _ _

/-- 元の Yoneda の P_Σ への因子化は、元の写像空間の作用で充満忠実。 -/
lemma sigmaYonedaInfinityMap_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (sigmaYonedaInfinityMap C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion_isFullyFaithful C).cancel_right
  rw [sigmaYonedaInfinityMap_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful C

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.8.10" (partial := component) "仮定：有限余積を持つ小準圏 C（HTT と一致）。結論：元の包含の左随伴の存在、Yoneda の同じ因子化と有限余積保存、および PΣ の sifted 余極限閉性という (1) の反射部分・(2)・(4)（一致）。反射の accessibility、任意の随伴との (3) の iff、(6) の compact generation はこの組には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion
