module

public import SerrePositivity.InfinityCategories.F1.TwistedArrowPointedDisplay
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection

/-!
概要：同じ全体の Tw からの pointed 比較は、両端固定の全ての fiber で同値。
方針：元の復元射の fiber 同値と、持ち上げ・縮小・普遍 pullback の三つの fiber 同型で分解する。
規約：構成済みの twistedArrowPointedDisplay 自体の fiber 写像を厳密に照合する。
使われ方：Tw の恒等点からの実際の輸送を普遍 pointed-space 輸送へ送って同値を検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

/-- 同じ全体の pointed 比較が、指定した両端の fiber に誘導する実際の射。 -/
def twistedArrowPointedDisplayFiber (C : SSet.{u}) [Quasicategory C]
    (b : (C.op ⊗ C) _⦋0⦌) :
    vertexFiber ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowProjection C)) (ULift.up b) ⟶
      vertexFiber pointedSpaceProjection
        ((twistedArrowHomInfinity C).app (Opposite.op ⦋0⦌) (ULift.up b)) :=
  transportSquareFiberMap ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowProjection C))
    pointedSpaceProjection (twistedArrowPointedDisplay C) (twistedArrowHomInfinity C)
    (twistedArrowPointedDisplay_projection C) (ULift.up b)

/-- 同じ fiber 射は、元の復元射の fiber 作用と三つの厳密な同型の合成そのもの。 -/
lemma twistedArrowPointedDisplayFiber_compare (C : SSet.{u}) [Quasicategory C]
    (b : (C.op ⊗ C) _⦋0⦌) :
    twistedArrowPointedDisplayFiber C b =
    (uliftVertexFiberIso.{u, u + 1} (twistedArrowProjection C) b).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (twistedArrowProjection C)
          (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
          (leftStraighteningInfinityReconstruction (twistedArrowProjection C))
          (leftStraighteningInfinityReconstruction_projection (twistedArrowProjection C)) b) ≫
      (smallLeftUnstraighteningFiberIso (twistedArrowHomInfinity C) b).hom ≫
      (leftUnstraighteningFiberIso (twistedArrowHomInfinity C) (ULift.up b)).hom := by
  apply vertexFiber_hom_ext pointedSpaceProjection
    ((twistedArrowHomInfinity C).app (Opposite.op ⦋0⦌) (ULift.up b))
  simp only [twistedArrowPointedDisplayFiber, Category.assoc]
  rw [transportSquareFiberMap_ι, leftUnstraighteningFiberIso_hom_ι]
  rw [← Category.assoc (smallLeftUnstraighteningFiberIso _ _).hom,
    smallLeftUnstraighteningFiberIso_hom_ι]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, vertexFiberMap_ι, Functor.map_comp]
  have h := congrArg (fun f ↦ f ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (leftStraighteningInfinityReconstruction (twistedArrowProjection C)) ≫
    (smallLeftUnstraighteningIso (twistedArrowHomInfinity C)).hom ≫
    pullback.fst pointedSpaceProjection (twistedArrowHomInfinity C))
    (uliftVertexFiberIso_inv_ι.{u, u + 1} (twistedArrowProjection C) b)
  simpa only [twistedArrowPointedDisplay, Category.assoc] using h.symm

/-- 同じ全体の pointed 比較の実際の fiber 作用は、全ての両端で同値。 -/
lemma twistedArrowPointedDisplayFiber_isQCatEquivalence (C : SSet.{u}) [Quasicategory C]
    (b : (C.op ⊗ C) _⦋0⦌) : IsQCatEquivalence (twistedArrowPointedDisplayFiber C b) := by
  rw [twistedArrowPointedDisplayFiber_compare]
  have h₁ := (qCatEquivalenceOfIso
    (uliftVertexFiberIso.{u, u + 1} (twistedArrowProjection C) b).symm).isQCatEquivalence
  have h₂ := (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
    (twistedArrowProjection C)
    (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
    (leftStraighteningInfinityReconstruction (twistedArrowProjection C))
    (leftStraighteningInfinityReconstruction_projection (twistedArrowProjection C))
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence
      (twistedArrowProjection C)) b).ulift.{u, u + 1}
  have h₃ := (qCatEquivalenceOfIso
    (smallLeftUnstraighteningFiberIso (twistedArrowHomInfinity C) b)).isQCatEquivalence
  have h₄ := (qCatEquivalenceOfIso
    (leftUnstraighteningFiberIso (twistedArrowHomInfinity C) (ULift.up b))).isQCatEquivalence
  exact h₁.comp (h₂.comp (h₃.comp h₄))

end SerrePositivity.InfinityCategories
