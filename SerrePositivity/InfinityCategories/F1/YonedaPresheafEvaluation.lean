module

public import SerrePositivity.InfinityCategories.F1.RepresentableUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.F1.SmallCoherentMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningFiber

/-!
概要：実際の Yoneda 対象前層から任意の前層への写像空間を、その前層の値と比較する。
方針：元の pinched Hom の unstraightening 比較、表現可能 coslice の恒等点評価、fiber の値を合成する。
規約：始域は同じ representablePresheafInfinity の前層 ∞ 圏内の実際の写像空間。
使われ方：Yoneda 補題の写像空間版と、同じ Yoneda 写像の充満忠実性への照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 実際の表現可能前層からの pinched Hom を、元の恒等錐で評価する写像。 -/
def yonedaPresheafEvaluation {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    pinchedHom (functorVertex (representablePresheafInfinity y)) (functorVertex F) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm y)))).obj :=
  leftUnstraighteningPinchedMappingSpaceMap (representablePresheafInfinity y) F ≫
    (smallLeftUnstraighteningRelativeFunctorIso (representablePresheafInfinity y) F).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (representableUnstraighteningEvaluation (smallLeftUnstraighteningProjection F) y) ≫
    (smallLeftUnstraighteningLiftedFiberValueEquivalence F (SSet.opObjEquiv.symm y)).hom

/-- Yoneda の実際の対象前層から任意の前層への写像空間は、その指定対象での値と同値。 -/
lemma yonedaPresheafEvaluation_isQCatEquivalence {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (yonedaPresheafEvaluation y F) := by
  have : ∀ n, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj C.op).obj n) :=
    fun n ↦ inferInstanceAs (Small.{u} (ULift.{u + 1} (C.op.obj n)))
  have h₁ := small_leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence
    (representablePresheafInfinity y) F
  have h₂ := (qCatEquivalenceOfIso
    (smallLeftUnstraighteningRelativeFunctorIso
      (representablePresheafInfinity y) F).symm).isQCatEquivalence
  have h₃ := (representableUnstraighteningEvaluation_isQCatEquivalence
    (smallLeftUnstraighteningProjection F) y).ulift.{u, u + 1}
  have h₄ := (smallLeftUnstraighteningLiftedFiberValueEquivalence F
    (SSet.opObjEquiv.symm y)).isQCatEquivalence
  exact h₁.comp (h₂.comp (h₃.comp h₄))

/-- Yoneda 補題の写像空間版。順方向は上で構成した同じ恒等点評価。 -/
def yonedaPresheafEvaluationEquivalence {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    QCatEquivalence
      (pinchedHom (functorVertex (representablePresheafInfinity y)) (functorVertex F))
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm y)))).obj) :=
  (yonedaPresheafEvaluation_isQCatEquivalence y F).choose

end SerrePositivity.InfinityCategories
