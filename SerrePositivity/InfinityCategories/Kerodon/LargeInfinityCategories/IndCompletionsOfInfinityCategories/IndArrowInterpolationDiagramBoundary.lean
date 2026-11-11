module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationCommaFamily

/-!
概要：元の試験族側で、補間した小さい全 C 図式が同じ元の C 図式に制限される。
方針：元の全円柱の境界等式を curry し、二つの宇宙同型を消去する。
規約：comma の全変換の一致は未主張。使われ方：元の q への境界回収。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationData κ D q)

/-- 元の全試験族側の coherent C 図式は、元の全 C 図式の同じ区間表示。 -/
lemma indArrowInterpolationCoherentDiagram_old :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationCoherentDiagram V =
        q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom ≫
          (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall.{u}).app ((SSet.uliftFunctor.{u + 1, u}).obj C) := by
  let T := (SSet.uliftFunctor.{u + 1, u}).obj A
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))
  apply uncurry_injective
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationCoherentDiagram, uncurry_curry]
  have hu := uncurry_pre_app ((SSet.uliftFunctor.{u + 1, u}).obj C)
    (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall.{u}
  simp only [Category.assoc] at hu
  rw [hu]
  have hb : (Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0])) ≫
      (β_ Δ[1] B).hom = (β_ Δ[1] T).hom ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ▷ Δ[1]) := by rfl
  have hf : (β_ (Δ[1] : SSet.{u + 1}) T).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall.{u} ▷ T := by rfl
  rw [← Category.assoc, hb, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationDiagram_old,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowOriginalFamily, ← Category.assoc, hf]

/-- 元の試験族側の小さい C 図式の持ち上げは、同じ元の全 C 図式に一致する。 -/
lemma indArrowInterpolationSmallDiagram_old :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationSmallDiagram V) =
        q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D := by
  let X := (SSet.uliftFunctor.{u + 1, u}).obj C
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1
  have he : (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall.{u}).app X ≫ (pre e.hom).app X = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall]
    change (pre (e.hom ≫ e.inv)).app X = 𝟙 _
    rw [Iso.hom_inv_id, pre_id]
    rfl
  have h := congrArg (fun f => f ≫ (pre e.hom).app X)
    (indArrowInterpolationCoherentDiagram_old V)
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationSmallDiagram_lift,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationLiftedDiagram]
  simpa only [X, e, Category.assoc, he, Category.comp_id] using h

/-- 元の試験族側で、帰還した comma 族は同じ元の C 全図式を厳密に保つ。 -/
lemma indArrowInterpolationCommaFamily_old_projection :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationCommaFamily V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D =
        q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationCommaFamily_projection]
  exact indArrowInterpolationSmallDiagram_old V

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
