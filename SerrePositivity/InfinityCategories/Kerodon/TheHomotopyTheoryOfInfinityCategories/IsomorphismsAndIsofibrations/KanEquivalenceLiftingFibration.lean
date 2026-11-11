module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreIsofibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 複体間で同値を右に持ち上げる射は、全ホーンを持ち上げる。
方針：Kan 複体と元の core の厳密な同型を作り、core の Kan fibration 性を移す。
規約：Fibration は全ホーンの持ち上げ性として使い、モデル圏の追加仮定を要求しない。
使われ方：両端固定の区間 Hom の同じ制限を Kan fibration にする。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- Kan 複体の元の core の包含は、同じ単体を保つ厳密な同型。 -/
def quasicategoryCoreIsoOfKan (X : SSet.{u}) [KanComplex X] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) ≅ X := by
  have : IsGroupoid (hoFunctor.obj X) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid X
  let h : ∀ s : X _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((𝟙 X : X ⟶ X).app _ s)) :=
    fun _ ↦ IsGroupoid.all_isIso (C := hoFunctor.obj X) _
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (𝟙 X) h, ?_, ?_⟩
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι, Category.comp_id, Category.id_comp]
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι (𝟙 X) h

/-- Kan 複体間の同じ射に対する同値の右持ち上げは、全ホーンの右持ち上げを与える。 -/
@[kerodon 01NW]
lemma fibration_of_kanEquivalenceLifting_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (p : X ⟶ Y)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) : Fibration p := by
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting p hp
  have h : (quasicategoryCoreIsoOfKan X).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p ≫
      (quasicategoryCoreIsoOfKan Y).hom = p := by
    change (quasicategoryCoreIsoOfKan X).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι = p
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc]
    change ((quasicategoryCoreIsoOfKan X).inv ≫ (quasicategoryCoreIsoOfKan X).hom) ≫ p = p
    rw [Iso.inv_hom_id, Category.id_comp]
  rw [← h]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
