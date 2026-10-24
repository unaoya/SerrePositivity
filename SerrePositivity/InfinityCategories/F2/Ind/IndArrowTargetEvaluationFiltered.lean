module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTargetUnderCocone
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeFilteredCriterion
/-!
概要：元の指定終点図式の下の実評価 comma は、任意の有限形状に対して filtered。
方針：指定変換を持つ元の試験族への余錐を、全ての大きい有限試験形状へ戻す。
規約：元の評価写像と全族を保持し、Kan 性を要求しない。
使われ方：終点評価の Quillen A における coslice の弱可縮性。
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
local notation "E" => diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
/-- 概要：終点評価の実引き戻しの任意の小さい試験族に、元の全族への余錐が存在する。
方針：元の相対余錐を回収する。規約：指定値を保持。使われ方：終点評価の cofinal 性。 -/
lemma nonempty_indArrowTargetEvaluationComma_cocone {A L : SSet.{u}}
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ pullback (sliceUnderProjection z) E) :
    Nonempty (JoinCocone q) := by
  have h : (q ≫ pullback.snd (sliceUnderProjection z) E) ≫ E =
      (q ≫ pullback.fst (sliceUnderProjection z) E) ≫ sliceUnderProjection z := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc := nonempty_indArrowTargetUnder_cocone κ D hA hL z
    (q ≫ pullback.snd (sliceUnderProjection z) E)
    (q ≫ pullback.fst (sliceUnderProjection z) E) h
  have hq : relativeCommaFamily E z (q ≫ pullback.fst (sliceUnderProjection z) E)
      (q ≫ pullback.snd (sliceUnderProjection z) E) h = q := by
    apply pullback.hom_ext <;> simp only [relativeCommaFamily, pullback.lift_fst,
      pullback.lift_snd]
  exact hq ▸ hc
/-- 概要：指定した κ-small な終点図式下の元の評価 comma は filtered。
方針：元の相対余錐を回収する。規約：指定値を保持。使われ方：終点評価の cofinal 性。 -/
lemma indArrowTargetEvaluationComma_isFiltered {L : SSet.{u}} (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) :
    IsFilteredInfinity (pullback (sliceUnderProjection z) E) := by
  apply isFilteredInfinity_of_liftedShape_cocones (Fact.out : κ.IsRegular)
  intro A hA q
  exact nonempty_indArrowTargetEvaluationComma_cocone κ D hA hL z q
end SerrePositivity.InfinityCategories.F2.Ind
