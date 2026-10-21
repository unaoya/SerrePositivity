module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteCoherentSpaceProducts
public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedConePointedRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafInfinity
public import SerrePositivity.InfinityCategories.F1.YonedaInfinityFullyFaithful

/-!
概要：元の Yoneda ∞ 関手を P_Σ(C) へ因子化する。
方針：元の表現可能前層の全錐の一点切断判定と、元の離散図式の極限の存在を使う。
規約：元の Yoneda 写像を包含後に厳密に回収し、別の Hom 前層に置き換えない。
使われ方：HTT 5.5.8.10、P_Σ の sifted 余極限による生成と普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の Yoneda 前層は、元の有限離散極限錐を全錐ごと保存する。 -/
lemma representablePresheafInfinity_preservesFiniteProducts
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    PreservesFiniteProductsFromSmallSource (representablePresheafInfinity y) := by
  intro J _ D c hc
  apply spaceCone_isLimit_of_pointRestriction_of_hasLimit
    (mapJoinCone (representablePresheafInfinity y) (JoinCone.ulift.{u, u + 1} c))
  · exact hasLimit_discreteCoherentSpaceDiagram _
  · exact representableNativeConePointedRestriction_isQCatEquivalence c hc y

/-- 元の Yoneda 前層は、元の P(C) 内で P_Σ の対象条件を満たす。 -/
lemma representablePresheafInfinity_isSigmaPresheaf
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsSigmaPresheaf (functorVertex (representablePresheafInfinity y)) :=
  (isSigmaPresheaf_object_iff _).mpr (representablePresheafInfinity_preservesFiniteProducts y)

/-- 元の Yoneda ∞ 関手を、元の対象と全高次の射を保って P_Σ(C) へ因子化。 -/
def sigmaYonedaInfinityMap (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SigmaPresheafInfinity C :=
  sigmaPresheafInfinityLift (yonedaInfinityMap C) (fun a ↦ by
    obtain ⟨a⟩ := a
    rw [yonedaInfinityMap_vertex]
    exact representablePresheafInfinity_isSigmaPresheaf a)

/-- P_Σ への因子化を包含すると、元の Yoneda ∞ 関手を厳密に回収する。 -/
lemma sigmaYonedaInfinityMap_inclusion (C : SSet.{u}) [Quasicategory C] :
    sigmaYonedaInfinityMap C ≫ sigmaPresheafInfinityInclusion C = yonedaInfinityMap C :=
  sigmaPresheafInfinityLift_inclusion _ _

/-- 元の Yoneda の P_Σ への因子化は、元の写像空間の作用で充満忠実。 -/
lemma sigmaYonedaInfinityMap_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    IsFullyFaithful (sigmaYonedaInfinityMap C) := by
  apply (sigmaPresheafInfinityInclusion_isFullyFaithful C).cancel_right
  rw [sigmaYonedaInfinityMap_inclusion]
  exact yonedaInfinityMap_isFullyFaithful C

end SerrePositivity.InfinityCategories.HomotopyLimits
