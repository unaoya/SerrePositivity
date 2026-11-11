module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 元の自由相対解像の固定対象の hammock の二重単体的図式

概要：各自由次数の元の hammock graph の余極限を、全単体作用素に沿う図式にする。
方針：元の固定対象表示を全語の二方向の図式へ代入し、語方向で余極限を取る。
規約：元の自由解像・全語・全作用素・元の余極限を保持する。
使われ方：DK 命題2.2の対角 hammock と左右の比較。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory CategoryTheory.Limits

def freeHammockWordDiagram (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) X Y

def freeHammockResolution (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    SimplicialObject SSet.{u} :=
  (freeHammockWordDiagram C X Y).flip ⋙ colim

lemma freeHammockResolution_obj (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (freeHammockResolution C X Y).obj n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n X) (freeResolutionObject C n Y) := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
