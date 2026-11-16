module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMap
public import SerrePositivity.EInfinity.Hammock.RelativeColimitMap

/-!
# 元の自由 hammock の左比較の係数自然性

概要：元の自由解像の augmentation の正方形を全 zigzag と全語へ移す。
方針：固定端点関手の合成と元の相対関手の自然性を使う。
規約：元の左比較射と元の係数写像を保持する。
使われ方：DK の高次比較の係数自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.EInfinity.Hammock
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)

lemma freeHammockFixedFunctor_augmentation (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap F).app n)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F n Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans D).app n)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation D n (F.functor.obj X))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation D n (F.functor.obj Y)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F := by
  have he := congrArg (fun K : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n ⟶ D => K.functor)
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_augmentation F) n)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_comp _ _ _ _ _ _).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_congr (w := w)
      (F := ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap F).app n).comp
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans D).app n))
      (G := ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).comp F) he _ _
      ((congrArg F.functor.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X)).trans rfl)
      ((congrArg F.functor.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y)).trans rfl)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_comp _ _ _ _ rfl rfl))

lemma freeHammockGraphMap_augmentation (X Y : C.category) :
    (flipFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word SimplexCategoryᵒᵖ SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockWordMap F X Y) ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockGraphAugmentation D (F.functor.obj X) (F.functor.obj Y) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockGraphAugmentation C X Y ≫
        (Functor.const SimplexCategoryᵒᵖ).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y) := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext w
  change nerveFunctor.map _ ≫ nerveFunctor.map _ =
    nerveFunctor.map _ ≫ nerveFunctor.map _
  rw [← nerveFunctor.map_comp, ← nerveFunctor.map_comp]
  apply congrArg nerveFunctor.map
  apply Cat.Hom.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockFixedFunctor_augmentation F X Y w n

lemma freeHammockMap_augmentation (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap F X Y ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation D (F.functor.obj X) (F.functor.obj Y) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation C X Y ≫
        (Functor.const SimplexCategoryᵒᵖ).map (Relative.colimitMap F X Y) := by
  apply NatTrans.ext
  funext n
  change colim.map _ ≫ colim.map _ = colim.map _ ≫ colim.map _
  rw [← colim.map_comp, ← colim.map_comp]
  apply congrArg colim.map
  exact NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockGraphMap_augmentation F X Y) n

lemma freeHammockDiagonalMap_augmentation (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation D (F.functor.obj X) (F.functor.obj Y) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y ≫ Relative.colimitMap F X Y := by
  apply NatTrans.ext
  funext n
  exact NatTrans.congr_app (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap_augmentation F X Y) n) n

lemma freeHammockDiagonalMap_reduction (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction D (F.functor.obj X) (F.functor.obj Y) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y ≫ Relative.reducedMap F X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction, Relative.reducedMap, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap_augmentation, Category.assoc]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
