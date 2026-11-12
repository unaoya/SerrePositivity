module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardBackwardRebuildMap

/-!
# 元の混合二方向の切断の全射の逆像と成分の回収

概要：元の通常 Hom と残りの全縦射から同じ元の射を回収する。
方針：接合点と全成分の回収で元の切断関手の充満性を示す。
規約：元の切断関手自体と指定部分圏の全射を保持する。
使われ方：DK9.4・10.3の元の混合二方向の分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
def forwardBackwardPreimage {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj S ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj T) : S ⟶ T :=
  eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild_functor_obj W w X Y S).symm ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuildMap W w X Y h ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild_functor_obj W w X Y T)

lemma forwardBackwardPreimage_app {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj S ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj T)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)).length + 1)) :
    HEq ((forwardBackwardPreimage W w X Y h).app j)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuildMap W w X Y h).app j) := by
  have hs := eqToHom_map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (W := W) j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild_functor_obj W w X Y S).symm
  have ht := eqToHom_map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (W := W) j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuild_functor_obj W w X Y T)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation] at hs ht
  dsimp only [forwardBackwardPreimage]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.comp_app, hs, ht, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

lemma forwardBackwardPreimage_joint {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj S ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).map
      (forwardBackwardPreimage W w X Y h)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap h := by
  apply WideSubcategory.hom_ext
  exact eq_of_heq ((forwardBackwardPreimage_app W w X Y h _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuildMap_joint W w X Y h))

lemma forwardBackwardPreimage_tail {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj S ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).obj T)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w).length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor W w X Y).map
      (forwardBackwardPreimage W w X Y h))).2.app j.succ =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap h).2.app j.succ := by
  exact eq_of_heq ((forwardBackwardPreimage_app W w X Y h _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardRebuildMap_tail W w X Y h j.succ))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
