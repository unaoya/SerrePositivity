module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeSectionTarget
public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportDiagramComparison
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedComparisonTransportExt
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramTriangleFaces

/-!
概要：全局所比較の両端図式を元の二重底変換で制限すると、元の二重・直接の分類図式。
方針：同じ全 section Hom の作用を各底対象で照合し、底の射の同じ値を使う。
規約：元の全相対 Hom と全ての底の射を保持する。
使われ方：元の大域結合比較の区間族の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 全局所比較の源を元の fibration に制限すると、同じ二重底変換の図式全体になる。 -/
lemma cocartesianBaseChangeNativeEnriched_sourceDiagram
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    ((cocartesianStrictTransportEnrichedDiagram A).precompose
      (isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))).precompose
        (cocartesianBaseChangeNativeEnriched l k) =
    (cocartesianStrictTransportEnrichedDiagram A).precompose
      ((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
        (cocartesianFibrationBaseChangeEnriched (nerveMap l))) := by
  have ho : ∀ a, _ := fun a ↦ show
    ((cocartesianBaseChangeNativeEnriched l k).comp SSet
      ((isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A))).comp SSet
        (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a)))))) =
    (((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
      (cocartesianFibrationBaseChangeEnriched (nerveMap l))).comp SSet
        (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a))))) from by
    refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
    intro p q
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  apply QuasicategoryEnrichedDiagram.extPointwise ho
  intro i j f
  exact QuasicategoryEnrichedComparison.heq_of_components (ho i) (ho j) _ _ (fun _ ↦ HEq.rfl)

/-- 全局所比較の終域を元の fibration に制限すると、同じ直接底変換の図式全体になる。 -/
lemma cocartesianBaseChangeNativeEnriched_targetDiagram
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    ((cocartesianStrictTransportEnrichedDiagram A).precompose
      (isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))).precompose
        (cocartesianBaseChangeNativeEnriched l k) =
    (cocartesianStrictTransportEnrichedDiagram A).precompose
      (cocartesianFibrationBaseChangeEnriched (nerveMap (l ⋙ k))) := by
  apply QuasicategoryEnrichedDiagram.extPointwise
    (fun a ↦ cocartesianBaseChangeNativeEnriched_sectionTarget l k a)
  intro i j f
  exact QuasicategoryEnrichedComparison.heq_of_components
    (cocartesianBaseChangeNativeEnriched_sectionTarget l k i)
    (cocartesianBaseChangeNativeEnriched_sectionTarget l k j) _ _ (fun _ ↦ HEq.rfl)

end SerrePositivity.InfinityCategories
