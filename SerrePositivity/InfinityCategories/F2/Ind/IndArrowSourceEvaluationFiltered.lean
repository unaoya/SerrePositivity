module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSourceUnderCocone
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeFilteredCriterion
public import SerrePositivity.InfinityCategories.Core.InnerPullback
/-!
概要：指定始点評価図式の下の実 under comma は filtered。
方針：任意の小さい試験族の実余錐を、全ての大きい有限試験形状へ移す。
規約：元の全射を保持し、追加の Kan 性を要求しない。
使われ方：始点評価の cofinal 性の Quillen A 入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
local notation "E" => diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
/-- 概要：元の指定始点評価図式の実 under comma は filtered。
方針：任意の小さい試験族の実余錐を、全ての大きい有限試験形状へ移す。
規約：元の全図式を保持。使われ方：始点評価の cofinal 性の Quillen A 入力。 -/
lemma indArrowSourceEvaluationComma_isFiltered {L : SSet.{u}} (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) :
    IsFilteredInfinity (pullback (sliceUnderProjection z) E) := by
  apply isFilteredInfinity_of_liftedShape_cocones (Fact.out : κ.IsRegular)
  intro A hA q
  exact nonempty_indArrowSourceEvaluationComma_cocone κ D hA hL z q
end SerrePositivity.InfinityCategories.F2.Ind
