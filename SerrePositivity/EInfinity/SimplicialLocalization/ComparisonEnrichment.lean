module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockUnit
public import SerrePositivity.EInfinity.SimplicialLocalization.Enrichment
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.EnrichedCategory
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitCompositionPointAssociativity

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

def HammockObjects (C : RelativeCategory.{u}) : Type u := C.category

instance hammockEnrichedCategory (C : RelativeCategory.{u}) :
    EnrichedCategory SSet.{u} (HammockObjects C) := by
  change EnrichedCategory SSet.{u} C.category
  exact enrichedCategory (C := C.category) C.weakEquivalences

def FreeHammockObjects (C : RelativeCategory.{u}) : Type u := C.category

instance freeHammockEnrichedCategory (C : RelativeCategory.{u}) :
    EnrichedCategory SSet.{u} (FreeHammockObjects C) where
  Hom X Y := freeHammockDiagonal C X Y
  id X := freeHammockDiagonalUnit C X
  comp X Y Z := freeHammockDiagonalComposition C X Y Z
  id_comp X Y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change composePoint ((freeResolution C).obj n).weakEquivalences
      (freeResolutionObject C n X) (freeResolutionObject C n X)
      (freeResolutionObject C n Y)
      ((colimitUnit ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n X)).app n PUnit.unit) f = f
    rw [← arrowPoint_identity]
    exact composePoint_identity_left _ f
  comp_id X Y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change composePoint ((freeResolution C).obj n).weakEquivalences
      (freeResolutionObject C n X) (freeResolutionObject C n Y)
      (freeResolutionObject C n Y) f
      ((colimitUnit ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n Y)).app n PUnit.unit) = f
    rw [← arrowPoint_identity]
    exact composePoint_identity_right _ f
  assoc V X Y Z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    exact composePoint_assoc ((freeResolution C).obj n).weakEquivalences q.1 q.2.1 q.2.2

end SerrePositivity.EInfinity.SimplicialLocalization
