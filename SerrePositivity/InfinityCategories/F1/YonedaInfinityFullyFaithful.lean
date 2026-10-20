module

public import SerrePositivity.InfinityCategories.F1.YonedaEvaluatedTransportEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostcompositionLaws
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostHomCriterion

/-!
概要：構成済みの同じ Yoneda ∞ 写像そのものは充満忠実。
方針：同じ恒等点での c1 評価と Tw の輸送の同値を、実際の区間後合成の可換式で消去する。
規約：独立な写像空間同値の存在ではなく、元の yonedaInfinityMap の Hom 作用を証明する。
使われ方：Kerodon 第8章の Yoneda 埋め込みと、表現可能前層による検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ Yoneda 写像の元の区間 Hom 作用を、対象前層の頂点表示に正規化する。 -/
def yonedaInfinityIntervalMappingSpaceMap {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    intervalMappingSpace (X := (SSet.uliftFunctor.{u + 1, u}).obj C) (ULift.up x) (ULift.up y) ⟶
      leftUnstraighteningTransformationSpace
        (representablePresheafInfinity x) (representablePresheafInfinity y) :=
  intervalMappingPostOfEq (yonedaInfinityMap C) (ULift.up x) (ULift.up y)
    (yonedaInfinityMap_vertex x) (yonedaInfinityMap_vertex y)

/-- 同じ Yoneda 写像の実際の区間 Hom 作用は、全ての対象対で同値。 -/
lemma yonedaInfinityIntervalMappingSpaceMap_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (yonedaInfinityIntervalMappingSpaceMap x y) := by
  let k := yonedaInfinityIntervalMappingSpaceMap x y
  have hcomp : k ≫
      intervalMappingPostOfEq (evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)))
        (functorVertex (representablePresheafInfinity x))
        (functorVertex (representablePresheafInfinity y))
        (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _) =
      intervalMappingPostOfEq
        (yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)))
        (ULift.up x) (ULift.up y)
        (yonedaInfinityMap_evaluate_vertex x x) (yonedaInfinityMap_evaluate_vertex x y) := by
    exact intervalMappingPostOfEq_comp _ _ _ _ _ _ _ _
      (yonedaInfinityMap_vertex x) (yonedaInfinityMap_vertex y)
      (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _)
  have e := (canonicalYonedaTransformationFiberEvaluation_parametrizedIso x
    (representablePresheafInfinity y)).precomp k
  simp only [← Category.assoc] at e
  rw [hcomp] at e
  have h := yonedaInfinityEvaluatedTransport_isQCatEquivalence x y
  have hc : IsQCatEquivalence
      (k ≫ canonicalYonedaTransformationFiberEvaluation x (representablePresheafInfinity y)) :=
    h.ofFunctorIso (by simpa only [Category.assoc] using e.symm)
  exact (canonicalYonedaTransformationFiberEvaluation_isQCatEquivalence x
    (representablePresheafInfinity y)).cancel_right hc

/-- 元の Yoneda ∞ 写像の標準 pinched Hom 作用そのものは、全ての対象対で同値。 -/
lemma yonedaInfinityMap_pinchedHomMap_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (pinchedHomMap (yonedaInfinityMap C) (ULift.up x) (ULift.up y)) := by
  apply pinchedHomMap_isQCatEquivalence_of_intervalPost (yonedaInfinityMap C)
    (ULift.up x) (ULift.up y) (yonedaInfinityMap_vertex x) (yonedaInfinityMap_vertex y)
  have h₁ := pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (X := (SSet.uliftFunctor.{u + 1, u}).obj C) (ULift.up x) (ULift.up y)
  have h₂ := yonedaInfinityIntervalMappingSpaceMap_isQCatEquivalence x y
  exact h₁.comp h₂

/-- 構成済みの同じ Yoneda ∞ 写像は、任意の小さい quasicategory に対して充満忠実。 -/
lemma yonedaInfinityMap_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    IsFullyFaithful (yonedaInfinityMap C) := by
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  exact (yonedaInfinityMap_pinchedHomMap_isQCatEquivalence x y).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
