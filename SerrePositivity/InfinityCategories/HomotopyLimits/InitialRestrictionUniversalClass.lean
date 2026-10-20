module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionUniversalCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.EvaluationFixedHomotopyTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowRightIdentityCancellation

/-!
概要：普遍前置から作る円柱が、元の制限円柱と同じ射の類を与えることを証明する。
方針：評価固定の三円柱の合成を底へ写し、全時刻定値な比較因子を消去する。
規約：元の raw な円柱を保持。使われ方：HL・HR の同じ類の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [LeftFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
  (hc : IsInitialVertex c)
local notation "D" => initialRestrictionHomCylinderData p q r hr d hd e y hc
local notation "U" => initialRestrictionUniversalCylinderData p q r hr d hd e y hc
local notation "C" => initialRestrictionSectionComparison p q r hr d hd e y hc
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)

/-- 普遍前置の円柱と元の HL・HR の制限円柱は、同じ射の類を与える。 -/
lemma initialRestrictionUniversalHomCylinder_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (initialRestrictionUniversalHomCylinder p q r hr d hd e y hc))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (initialRestrictionHomCylinder p q r hr d hd e y hc))) := by
  let O := homotopyEndpointTransport (D).homotopy
    (congrArg (· ≫ leftFibrationInitialSection q c hc y)
      (initialRestrictionEdgeFamily_vertexFiberLift p q r hr d hd e y)) rfl
  have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  have hoev : O.h ≫ leftFibrationInitialEvaluation q c y =
      fst (vertexFiber p y) Δ[1] ≫ vertexFiberMap p q r hr y := by
    dsimp only [O]
    rw [homotopyEndpointTransport_raw]
    exact initialRestrictionHomCylinderData_evaluation p q r hr d hd e y hc
  have ht := evaluationFixedHomotopyTriangle_homMk_comp
    (leftFibrationInitialEvaluation q c y) (U).homotopy C O (vertexFiberMap p q r hr y)
    (U).evaluation (initialRestrictionSectionComparison_evaluation p q r hr d hd e y hc) hoev
  let G := (hoFunctor.map ((ihom (vertexFiber p y)).map P)).toFunctor
  have hg := congrArg G.map ht
  rw [G.map_comp] at hg
  have hcbase : (C).h ≫ P = fst (vertexFiber p y) Δ[1] ≫ (D).lift ≫ P := by
    rw [← Category.assoc (C).h (leftFibrationInitialProjection q c y),
      initialRestrictionSectionComparison_base]
    simp only [Category.assoc]
  have hC := homotopyIso_postcomp_constant_arrow C P ((D).lift ≫ P) hcbase
  rw [functorIso_postcomp_hom] at hC
  have ha := arrowRightIdentity_cancel _ _ _ hg hC
  have hu := kanFunctorHomotopy_hom_arrow_of_h_eq
    (initialRestrictionUniversalHomCylinder p q r hr d hd e y hc)
    (functorHomotopyPostcomp (U).homotopy P)
    (initialRestrictionUniversalHomCylinder_projection p q r hr d hd e y hc)
  have ho := kanFunctorHomotopy_hom_arrow_of_h_eq
    (initialRestrictionHomCylinder p q r hr d hd e y hc)
    (functorHomotopyPostcomp O P)
    (by
      dsimp only [O, functorHomotopyPostcomp]
      rw [homotopyEndpointTransport_raw]
      exact initialRestrictionHomCylinder_projection p q r hr d hd e y hc)
  rw [functorHomotopyPostcomp_hom] at hu ho
  exact hu.trans (ha.trans ho.symm)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
