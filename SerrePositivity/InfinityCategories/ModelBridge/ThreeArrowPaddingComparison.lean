module

public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingAction
public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingNerve
public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowEquivalence
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Diagram

/-!
# 元の三列の二つの padding 比較の anodyne 反転後の一致

概要：元の graph の外側・内側の二つの写像は、anodyne を反転する関手の下で一致する。
方針：元の三本矢からの包含で配置のホモトピーを回収し、その圏同値の像を消去する。
規約：明示的な配置だけでなく、元の graphDiagram の比較射自身の像を比較する。
使われ方：元の三列の標準射と padding 余極限への比較の接続。
-/

@[expose] public section
universe u v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory HomotopicalAlgebra FrameHom

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma original_maps_after_threeArrow_image_eq :
    L.map (nerveMap (ThreeArrow.functor (X := X) (Y := Y)) ≫
        (graphDiagram (weakEquivalences C) X Y).map outerWordMap) =
      L.map (nerveMap (ThreeArrow.functor (X := X) (Y := Y)) ≫
        (graphDiagram (weakEquivalences C) X Y).map innerWordMap) := by
  change L.map (nerveMap (ThreeArrow.functor ⋙ WordAction.functor outerWordMap)) =
    L.map (nerveMap (ThreeArrow.functor ⋙ WordAction.functor innerWordMap))
  rw [outer_action_functor, inner_action_functor]
  exact outer_inner_image_eq L hL

include hL in
lemma original_maps_image_eq :
    L.map ((graphDiagram (weakEquivalences C) X Y).map outerWordMap) =
      L.map ((graphDiagram (weakEquivalences C) X Y).map innerWordMap) := by
  let he := NerveEquivalenceImage.imageIso (ThreeArrow.equivalence X Y) L hL
  have hi := he.isIso_hom
  change IsIso (L.map (nerveMap (ThreeArrow.functor (X := X) (Y := Y)))) at hi
  apply (cancel_epi (L.map (nerveMap (ThreeArrow.functor (X := X) (Y := Y))))).1
  simpa only [CategoryTheory.Functor.map_comp] using
    original_maps_after_threeArrow_image_eq X Y L hL

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
