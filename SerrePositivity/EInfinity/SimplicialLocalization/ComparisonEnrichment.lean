module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockUnit
public import SerrePositivity.EInfinity.SimplicialLocalization.Enrichment
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPointAssociativity

/-!
# 元の自由 hammock 対角と hammock の実単体的豊穣圏

概要：元の対角の空語の単位と連結合成を全公理のある豊穣圏へ束ねる。
方針：各次数の実点の単位・結合則を使用する。
規約：元の圏の通常の Category instance を変更しない。
使われ方：元の左右比較を実際の豊穣関手にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory MonoidalCategory Hammock

def HammockObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : Type u := C.category

instance hammockEnrichedCategory (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    EnrichedCategory SSet.{u} (HammockObjects C) := by
  change EnrichedCategory SSet.{u} C.category
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedCategory.enrichedCategory (C := C.category) C.weakEquivalences

def FreeHammockObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : Type u := C.category

instance freeHammockEnrichedCategory (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    EnrichedCategory SSet.{u} (FreeHammockObjects C) where
  Hom X Y := freeHammockDiagonal C X Y
  id X := freeHammockDiagonalUnit C X
  comp X Y Z := freeHammockDiagonalComposition C X Y Z
  id_comp X Y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint ((freeResolution C).obj n).weakEquivalences
      (freeResolutionObject C n X) (freeResolutionObject C n X)
      (freeResolutionObject C n Y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n X)).app n PUnit.unit) f = f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_left _ f
  comp_id X Y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint ((freeResolution C).obj n).weakEquivalences
      (freeResolutionObject C n X) (freeResolutionObject C n Y)
      (freeResolutionObject C n Y) f
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n Y)).app n PUnit.unit) = f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_right _ f
  assoc V X Y Z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_assoc ((freeResolution C).obj n).weakEquivalences q.1 q.2.1 q.2.2

end SerrePositivity.EInfinity.SimplicialLocalization
