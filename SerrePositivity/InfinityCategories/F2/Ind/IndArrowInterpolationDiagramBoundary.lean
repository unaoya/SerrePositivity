module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationCommaFamily

/-!
概要：元の試験族側で、補間した小さい全 C 図式が同じ元の C 図式に制限される。
方針：元の全円柱の境界等式を curry し、二つの宇宙同型を消去する。
規約：comma の全変換の一致は未主張。使われ方：元の q への境界回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 元の全試験族側の coherent C 図式は、元の全 C 図式の同じ区間表示。 -/
lemma indArrowInterpolationCoherentDiagram_old :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ≫
      indArrowInterpolationCoherentDiagram V =
        q ≫ diagramCommaProjection κ D ≫ (uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom ≫
          (pre liftedIntervalToSmall.{u}).app ((SSet.uliftFunctor.{u + 1, u}).obj C) := by
  let T := (SSet.uliftFunctor.{u + 1, u}).obj A
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  apply uncurry_injective
  rw [uncurry_natural_left, indArrowInterpolationCoherentDiagram, uncurry_curry]
  have hu := uncurry_pre_app ((SSet.uliftFunctor.{u + 1, u}).obj C)
    (q ≫ diagramCommaProjection κ D ≫ (uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom)
    liftedIntervalToSmall.{u}
  simp only [Category.assoc] at hu
  rw [hu]
  have hb : (Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0])) ≫
      (β_ Δ[1] B).hom = (β_ Δ[1] T).hom ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ▷ Δ[1]) := by rfl
  have hf : (β_ (Δ[1] : SSet.{u + 1}) T).hom ≫ liftedIntervalFlip T =
      liftedIntervalToSmall.{u} ▷ T := by rfl
  rw [← Category.assoc, hb, Category.assoc, indArrowInterpolationDiagram_old,
    indArrowOriginalFamily, ← Category.assoc, hf]

/-- 元の試験族側の小さい C 図式の持ち上げは、同じ元の全 C 図式に一致する。 -/
lemma indArrowInterpolationSmallDiagram_old :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) =
        q ≫ diagramCommaProjection κ D := by
  let X := (SSet.uliftFunctor.{u + 1, u}).obj C
  let e := HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 1
  have he : (pre liftedIntervalToSmall.{u}).app X ≫ (pre e.hom).app X = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← pre_map, liftedIntervalToSmall]
    change (pre (e.hom ≫ e.inv)).app X = 𝟙 _
    rw [Iso.hom_inv_id, pre_id]
    rfl
  have h := congrArg (fun f => f ≫ (pre e.hom).app X)
    (indArrowInterpolationCoherentDiagram_old V)
  apply (cancel_mono (uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom).mp
  rw [Category.assoc, indArrowInterpolationSmallDiagram_lift,
    indArrowInterpolationLiftedDiagram]
  simpa only [X, e, Category.assoc, he, Category.comp_id] using h

/-- 元の試験族側で、帰還した comma 族は同じ元の C 全図式を厳密に保つ。 -/
lemma indArrowInterpolationCommaFamily_old_projection :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ≫
      indArrowInterpolationCommaFamily V ≫ diagramCommaProjection κ D =
        q ≫ diagramCommaProjection κ D := by
  rw [indArrowInterpolationCommaFamily_projection]
  exact indArrowInterpolationSmallDiagram_old V

end SerrePositivity.InfinityCategories.F2.Ind
