module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSourceValues
/-!
概要：補間した全図式と全余錐の終点評価は、元の全円柱の終点面。
方針：curry の終点評価と同じ宇宙比較の可換性を使う。
規約：全パラメーターで元の全射を保持する。
使われ方：元の実 comma 全族の終点評価の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：区間の宇宙比較は同じ元の終点での評価を保つ。
方針：前合成の自然性を使う。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma arrowDiagramUniverseRestriction_evaluate_one (X : SSet.{u + 1}) :
    arrowDiagramUniverseRestriction X ≫
      evaluateFunctorAt (Y := X) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))) =
      evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.{u+1}.symm (1 : Fin 2)) := by
  rw [arrowDiagramUniverseRestriction, evaluateFunctorAt_pre]
  rfl
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
/-- 概要：持ち上げた元の全図式の評価は円柱の同じ終点面。
方針：curry を評価する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma indArrowInterpolationLiftedDiagram_target : indArrowInterpolationLiftedDiagram V ≫
    evaluateFunctorAt (Y := (SSet.uliftFunctor.{u + 1, u}).obj C)
      (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))) =
      SSet.ι₁ ≫ indArrowInterpolationDiagram V := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  change (curry ((β_ (Δ[1] : SSet.{u + 1}) B).hom ≫ indArrowInterpolationDiagram V) ≫
    arrowDiagramUniverseRestriction _) ≫ _ = _
  rw [Category.assoc, arrowDiagramUniverseRestriction_evaluate_one,
    curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_one_braiding]
/-- 概要：持ち上げた全余錐の評価も同じ全終点面。
方針：全円柱の curry を評価する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma indArrowInterpolationLiftedCoconeMap_target : indArrowInterpolationLiftedCoconeMap V ≫
    evaluateFunctorAt (Y := IndInfinity κ C)
      (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))) =
    SSet.ι₁ ≫ indArrowInterpolationSquare V := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  change (curry ((β_ (Δ[1] : SSet.{u + 1}) (join B Δ[0])).hom ≫
    indArrowInterpolationSquare V) ≫ arrowDiagramUniverseRestriction _) ≫ _ = _
  rw [Category.assoc, arrowDiagramUniverseRestriction_evaluate_one,
    curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_one_braiding]
end SerrePositivity.InfinityCategories.F2.Ind
