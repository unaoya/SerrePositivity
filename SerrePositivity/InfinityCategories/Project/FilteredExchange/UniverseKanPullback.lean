module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseLeftFibration

/-!
概要：Kan fibration と元の厳密な引き戻しの宇宙持ち上げ。
方針：元のホーン充填を持ち上げ、点ごとの極限保存を適用する。
規約：元の二射影を保持。使われ方：小さい実 fiber 模型と大きい切断模型の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 全ホーンの相対充填性は任意の宇宙持ち上げで保たれる。 -/
lemma uliftMap_fibration {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration ((SSet.uliftFunctor.{v, u}).map p) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨j⟩⟩ := hi
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_hasLiftingProperty_horn p n j

/-- 単体集合の宇宙持ち上げは、通常の cospan の極限を保つ。 -/
lemma uliftFunctor_preservesCospanLimits :
    PreservesLimitsOfShape WalkingCospan (SSet.uliftFunctor.{v, u}) := by
  change PreservesLimitsOfShape WalkingCospan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj CategoryTheory.uliftFunctor.{v, u})
  infer_instance

variable {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- 元の引き戻しの持ち上げと、持ち上げた二射の引き戻しの標準同型。 -/
def uliftPullbackIso : (SSet.uliftFunctor.{v, u}).obj (pullback f g) ≅
    pullback ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) := by
  have := uliftFunctor_preservesCospanLimits.{u, v}
  exact PreservesPullback.iso _ f g

/-- 標準同型は元の第一射影の持ち上げを保つ。 -/
lemma uliftPullbackIso_fst : (uliftPullbackIso.{u, v} f g).hom ≫ pullback.fst _ _ =
    (SSet.uliftFunctor.{v, u}).map (pullback.fst f g) := by
  have := uliftFunctor_preservesCospanLimits.{u, v}
  exact PreservesPullback.iso_hom_fst _ f g

/-- 第二射影も同じ元の射の持ち上げ。 -/
lemma uliftPullbackIso_snd : (uliftPullbackIso.{u, v} f g).hom ≫ pullback.snd _ _ =
    (SSet.uliftFunctor.{v, u}).map (pullback.snd f g) := by
  have := uliftFunctor_preservesCospanLimits.{u, v}
  exact PreservesPullback.iso_hom_snd _ f g

end SerrePositivity.InfinityCategories.Project.FilteredExchange
