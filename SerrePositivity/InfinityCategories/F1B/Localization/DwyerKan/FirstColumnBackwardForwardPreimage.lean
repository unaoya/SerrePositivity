module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardForwardRebuildMap

/-!
# 元の混合二方向 −+ の切断の全射の逆像と成分の回収

概要：元の指定 Hom と残りの全縦射から同じ元の射を回収する。
方針：接合点と全成分の回収で元の切断関手の充満性を示す。
規約：元の切断関手自体と指定部分圏の全射を保持する。
使われ方：DK9.4・10.3の元の混合二方向 −+の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : Word) (X Y : C)
def backwardForwardPreimage {S T : backwardForwardSource W w X Y}
    (h : (backwardForwardFunctor W w X Y).obj S ⟶
      (backwardForwardFunctor W w X Y).obj T) : S ⟶ T :=
  eqToHom (backwardForwardRebuild_functor_obj W w X Y S).symm ≫
    backwardForwardRebuildMap W w X Y h ≫ eqToHom (backwardForwardRebuild_functor_obj W w X Y T)

lemma backwardForwardPreimage_app {S T : backwardForwardSource W w X Y}
    (h : (backwardForwardFunctor W w X Y).obj S ⟶ (backwardForwardFunctor W w X Y).obj T)
    (j : Fin ((Word.append (Word.single .backward) (Word.cons .forward w)).length + 1)) :
    HEq ((backwardForwardPreimage W w X Y h).app j)
      ((backwardForwardRebuildMap W w X Y h).app j) := by
  have hs := eqToHom_map (Zigzag.evaluation (W := W) j)
    (backwardForwardRebuild_functor_obj W w X Y S).symm
  have ht := eqToHom_map (Zigzag.evaluation (W := W) j)
    (backwardForwardRebuild_functor_obj W w X Y T)
  dsimp only [Zigzag.evaluation] at hs ht
  dsimp only [backwardForwardPreimage]
  simp only [Zigzag.comp_app, hs, ht, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

lemma backwardForwardPreimage_joint {S T : backwardForwardSource W w X Y}
    (h : (backwardForwardFunctor W w X Y).obj S ⟶ (backwardForwardFunctor W w X Y).obj T) :
    TwoSidedGrothendieck.baseMap ((backwardForwardFunctor W w X Y).map
      (backwardForwardPreimage W w X Y h)) = TwoSidedGrothendieck.baseMap h := by
  apply WideSubcategory.hom_ext
  exact eq_of_heq ((backwardForwardPreimage_app W w X Y h _).trans
    (backwardForwardRebuildMap_joint W w X Y h))

lemma backwardForwardPreimage_tail {S T : backwardForwardSource W w X Y}
    (h : (backwardForwardFunctor W w X Y).obj S ⟶ (backwardForwardFunctor W w X Y).obj T)
    (j : Fin (Word.cons .forward w).length) :
    (TwoSidedGrothendieck.leftMap ((backwardForwardFunctor W w X Y).map
      (backwardForwardPreimage W w X Y h))).2.app j.succ =
        (TwoSidedGrothendieck.leftMap h).2.app j.succ := by
  exact eq_of_heq ((backwardForwardPreimage_app W w X Y h _).trans
    (backwardForwardRebuildMap_tail W w X Y h j.succ))

end SerrePositivity.EInfinity.Hammock.FirstColumn
