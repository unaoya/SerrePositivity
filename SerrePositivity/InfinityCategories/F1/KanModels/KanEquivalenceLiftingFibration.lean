module

public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoreIsofibration

/-!
概要：Kan 複体間で同値を右に持ち上げる射は、全ホーンを持ち上げる。
方針：Kan 複体と元の core の厳密な同型を作り、core の Kan fibration 性を移す。
規約：Fibration は全ホーンの持ち上げ性として使い、モデル圏の追加仮定を要求しない。
使われ方：両端固定の区間 Hom の同じ制限を Kan fibration にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- Kan 複体の元の core の包含は、同じ単体を保つ厳密な同型。 -/
def quasicategoryCoreIsoOfKan (X : SSet.{u}) [KanComplex X] :
    (quasicategoryCore X : SSet.{u}) ≅ X := by
  have : IsGroupoid (hoFunctor.obj X) := kanComplex_ho_isGroupoid X
  let h : ∀ s : X _⦋1⦌, IsInvertibleEdge (edgeOfSimplex ((𝟙 X : X ⟶ X).app _ s)) :=
    fun _ ↦ IsGroupoid.all_isIso (C := hoFunctor.obj X) _
  refine ⟨(quasicategoryCore X).ι, quasicategoryCoreLift (𝟙 X) h, ?_, ?_⟩
  · apply (cancel_mono (quasicategoryCore X).ι).mp
    rw [Category.assoc, quasicategoryCoreLift_ι, Category.comp_id, Category.id_comp]
  · exact quasicategoryCoreLift_ι (𝟙 X) h

/-- Kan 複体間の同じ射に対する同値の右持ち上げは、全ホーンの右持ち上げを与える。 -/
lemma fibration_of_kanEquivalenceLifting_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (p : X ⟶ Y)
    (hp : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting p) : Fibration p := by
  have : Fibration (quasicategoryCoreMap p) :=
    F2.coreMap_fibration_of_kanEquivalenceLifting p hp
  have h : (quasicategoryCoreIsoOfKan X).inv ≫ quasicategoryCoreMap p ≫
      (quasicategoryCoreIsoOfKan Y).hom = p := by
    change (quasicategoryCoreIsoOfKan X).inv ≫ quasicategoryCoreMap p ≫
      (quasicategoryCore Y).ι = p
    rw [quasicategoryCoreMap_ι, ← Category.assoc]
    change ((quasicategoryCoreIsoOfKan X).inv ≫ (quasicategoryCoreIsoOfKan X).hom) ≫ p = p
    rw [Iso.inv_hom_id, Category.id_comp]
  rw [← h]
  infer_instance

end SerrePositivity.InfinityCategories
