module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockMap
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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory CategoryTheory.Limits Hammock
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)

lemma freeHammockFixedFunctor_augmentation (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) ((freeResolutionMap F).app n)
        (freeResolutionMap_object F n X) (freeResolutionMap_object F n Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans D).app n)
        (freeResolutionObject_augmentation D n (F.functor.obj X))
        (freeResolutionObject_augmentation D n (F.functor.obj Y)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
        (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F := by
  have he := congrArg (fun K : (freeResolution C).obj n ⟶ D => K.functor)
    (NatTrans.congr_app (freeResolutionMap_augmentation F) n)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_comp _ _ _ _ _ _).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_congr (w := w)
      (F := ((freeResolutionMap F).app n).comp
        ((freeResolutionAugmentationNatTrans D).app n))
      (G := ((freeResolutionAugmentationNatTrans C).app n).comp F) he _ _
      ((congrArg F.functor.obj (freeResolutionObject_augmentation C n X)).trans rfl)
      ((congrArg F.functor.obj (freeResolutionObject_augmentation C n Y)).trans rfl)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_comp _ _ _ _ rfl rfl))

lemma freeHammockGraphMap_augmentation (X Y : C.category) :
    (flipFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word SimplexCategoryᵒᵖ SSet.{u}).map (freeHammockWordMap F X Y) ≫
        freeHammockGraphAugmentation D (F.functor.obj X) (F.functor.obj Y) =
      freeHammockGraphAugmentation C X Y ≫
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
  exact freeHammockFixedFunctor_augmentation F X Y w n

lemma freeHammockMap_augmentation (X Y : C.category) :
    freeHammockMap F X Y ≫
        freeHammockAugmentation D (F.functor.obj X) (F.functor.obj Y) =
      freeHammockAugmentation C X Y ≫
        (Functor.const SimplexCategoryᵒᵖ).map (Relative.colimitMap F X Y) := by
  apply NatTrans.ext
  funext n
  change colim.map _ ≫ colim.map _ = colim.map _ ≫ colim.map _
  rw [← colim.map_comp, ← colim.map_comp]
  apply congrArg colim.map
  exact NatTrans.congr_app (freeHammockGraphMap_augmentation F X Y) n

lemma freeHammockDiagonalMap_augmentation (X Y : C.category) :
    freeHammockDiagonalMap F X Y ≫
        freeHammockDiagonalAugmentation D (F.functor.obj X) (F.functor.obj Y) =
      freeHammockDiagonalAugmentation C X Y ≫ Relative.colimitMap F X Y := by
  apply NatTrans.ext
  funext n
  exact NatTrans.congr_app (NatTrans.congr_app (freeHammockMap_augmentation F X Y) n) n

lemma freeHammockDiagonalMap_reduction (X Y : C.category) :
    freeHammockDiagonalMap F X Y ≫
        freeHammockDiagonalReduction D (F.functor.obj X) (F.functor.obj Y) =
      freeHammockDiagonalReduction C X Y ≫ Relative.reducedMap F X Y := by
  simp only [freeHammockDiagonalReduction, Relative.reducedMap, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, freeHammockDiagonalMap_augmentation, Category.assoc]

end SerrePositivity.EInfinity.SimplicialLocalization
