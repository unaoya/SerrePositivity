module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationCommaFamily
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowNormalizedPrismCurry
/-!
概要：補間した元の図式と全余錐の始点評価を、指定始点余錐へ戻す。
方針：右円柱の始点境界を curry・宇宙移送・小さい図式の順に回収する。
規約：同じ元の全射の厳密な等式。使われ方：指定始点下での実 comma 族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
/-- 概要：元の補間図式の始点は、指定始点余錐の同じ小さい図式。
方針：右円柱の始点境界を射影する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma indArrowInterpolationDiagram_source : SSet.ι₀ ≫ indArrowInterpolationDiagram V =
    V.sourceCone ≫ pullback.fst (indYoneda κ C) (sliceOverProjection D) := by
  rw [indArrowInterpolationDiagram, ← Category.assoc,
    indArrowInterpolationRawCylinder_source, indArrowSourceEndpointRaw_projection]
/-- 概要：宇宙移送した全図式の始点評価も、同じ指定小図式。
方針：curry の評価と宇宙移送の可換性を使う。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma indArrowInterpolationLiftedDiagram_source : indArrowInterpolationLiftedDiagram V ≫
    evaluateFunctorAt (Y := (SSet.uliftFunctor.{u + 1, u}).obj C)
      (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) =
    V.sourceCone ≫ pullback.fst (indYoneda κ C) (sliceOverProjection D) := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  change (curry ((β_ (Δ[1] : SSet.{u + 1}) B).hom ≫ indArrowInterpolationDiagram V) ≫
    arrowDiagramUniverseRestriction _) ≫ _ = _
  rw [Category.assoc, arrowDiagramUniverseRestriction_evaluate_zero,
    curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_zero_braiding,
    indArrowInterpolationDiagram, ← Category.assoc,
    indArrowInterpolationRawCylinder_source, indArrowSourceEndpointRaw_projection]
/-- 概要：全余錐の始点評価は、指定始点余錐の同じ点制限。
方針：全正方形の始点境界を評価する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma indArrowInterpolationLiftedCoconeMap_source : indArrowInterpolationLiftedCoconeMap V ≫
    evaluateFunctorAt (Y := IndInfinity κ C)
      (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) =
    sliceOverUncurry (V.sourceCone ≫ pullback.snd (indYoneda κ C) (sliceOverProjection D) ≫
      sliceOverRestrict D (diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))) := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  change (curry ((β_ (Δ[1] : SSet.{u + 1}) (join B Δ[0])).hom ≫
    indArrowInterpolationSquare V) ≫ arrowDiagramUniverseRestriction _) ≫ _ = _
  rw [Category.assoc, arrowDiagramUniverseRestriction_evaluate_zero,
    curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_zero_braiding,
    indArrowInterpolationSquare_source]
/-- 概要：小さい補間図式の始点評価は、同じ指定小図式。
方針：宇宙持ち上げ後の評価を回収する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma indArrowInterpolationSmallDiagram_source :
    (SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) =
    V.sourceCone ≫ pullback.fst (indYoneda κ C) (sliceOverProjection D) := by
  rw [← indArrowFunctorSpace_evaluate (C := C), ← Category.assoc,
    indArrowInterpolationSmallDiagram_lift]
  exact indArrowInterpolationLiftedDiagram_source V

end SerrePositivity.InfinityCategories.F2.Ind
