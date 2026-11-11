module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockObjectMap
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHammockMap

/-!
# 元の自由 hammock の係数写像

概要：元の相対関手を自由 hammock の全語・全次数・対角へ移す。
方針：証明済みの選択対象の自然性を一般の固定対象写像へ代入する。
規約：元の自由解像と全語の余極限を保持する。
使われ方：DK の左右比較射の係数自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory CategoryTheory.Limits
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)

def freeHammockWordMap (X Y : C.category) : freeHammockWordDiagram C X Y ⟶
    freeHammockWordDiagram D (F.functor.obj X) (F.functor.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectCategoryMap.graphWordMap (freeResolution C) (freeResolution D)
    (freeResolutionObject C) (freeResolutionObject D)
    (fun θ X => freeResolutionObject_naturality C θ X)
    (fun θ X => freeResolutionObject_naturality D θ X)
    (freeResolutionMap F) F.functor.obj (freeResolutionMap_object F) X Y

def freeHammockMap (X Y : C.category) : freeHammockResolution C X Y ⟶
    freeHammockResolution D (F.functor.obj X) (F.functor.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.hammockMap (freeResolution C) (freeResolution D)
    (freeResolutionObject C) (freeResolutionObject D)
    (fun θ X => freeResolutionObject_naturality C θ X)
    (fun θ X => freeResolutionObject_naturality D θ X)
    (freeResolutionMap F) F.functor.obj (freeResolutionMap_object F) X Y

def freeHammockDiagonalMap (X Y : C.category) : freeHammockDiagonal C X Y ⟶
    freeHammockDiagonal D (F.functor.obj X) (F.functor.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (freeHammockMap F X Y)

lemma freeHammockMap_inclusion (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (freeHammockWordMap F X Y).app w ≫
        (pointwiseCocone
          (freeHammockWordDiagram D (F.functor.obj X) (F.functor.obj Y))).ι.app w =
      (pointwiseCocone (freeHammockWordDiagram C X Y)).ι.app w ≫ freeHammockMap F X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.hammockMap_inclusion _ _ _ _ _ _ _ _ _ X Y w

lemma freeHammockDiagonalMap_inclusion (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map ((freeHammockWordMap F X Y).app w) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map ((pointwiseCocone
          (freeHammockWordDiagram D (F.functor.obj X) (F.functor.obj Y))).ι.app w) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
        ((pointwiseCocone (freeHammockWordDiagram C X Y)).ι.app w) ≫
          freeHammockDiagonalMap F X Y := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map_comp _ _).symm.trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (freeHammockMap_inclusion F X Y w)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map_comp _ _))

end SerrePositivity.EInfinity.SimplicialLocalization
