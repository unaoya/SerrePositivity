module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowIntervalEndpointPair
/-!
概要：同じ二合成対角から矢印 Hom へ戻す同型も二つの可変辺を保持する。
方針：既存の逆向きの射影則を同じ同型で相殺する。
規約：四頂点・全区間族・二入力の順序を保持する。
使われ方：正本の底座標を同じ合成対応の endpoint pair へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)
lemma dgGluingArrowCompositionIso_hom_endpoints :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso f g).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowIntervalEndpointPair f g =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionEndpointPair f g := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso f g).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowIntervalEndpointPair_components]
  simpa only [Category.id_comp] using
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso_inv_endpoints f g (𝟙 _)).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
