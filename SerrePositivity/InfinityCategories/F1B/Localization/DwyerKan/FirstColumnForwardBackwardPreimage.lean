module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardBackwardRebuildMap

/-!
# 元の混合二方向の切断の全射の逆像と成分の回収

概要：元の通常 Hom と残りの全縦射から同じ元の射を回収する。
方針：接合点と全成分の回収で元の切断関手の充満性を示す。
規約：元の切断関手自体と指定部分圏の全射を保持する。
使われ方：DK9.4・10.3の元の混合二方向の分解。
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
def forwardBackwardPreimage {S T : forwardBackwardSource W w X Y}
    (h : (forwardBackwardFunctor W w X Y).obj S ⟶
      (forwardBackwardFunctor W w X Y).obj T) : S ⟶ T :=
  eqToHom (forwardBackwardRebuild_functor_obj W w X Y S).symm ≫
    forwardBackwardRebuildMap W w X Y h ≫ eqToHom (forwardBackwardRebuild_functor_obj W w X Y T)

lemma forwardBackwardPreimage_app {S T : forwardBackwardSource W w X Y}
    (h : (forwardBackwardFunctor W w X Y).obj S ⟶ (forwardBackwardFunctor W w X Y).obj T)
    (j : Fin ((Word.append (Word.single .forward) (Word.cons .backward w)).length + 1)) :
    HEq ((forwardBackwardPreimage W w X Y h).app j)
      ((forwardBackwardRebuildMap W w X Y h).app j) := by
  have hs := eqToHom_map (Zigzag.evaluation (W := W) j)
    (forwardBackwardRebuild_functor_obj W w X Y S).symm
  have ht := eqToHom_map (Zigzag.evaluation (W := W) j)
    (forwardBackwardRebuild_functor_obj W w X Y T)
  dsimp only [Zigzag.evaluation] at hs ht
  dsimp only [forwardBackwardPreimage]
  simp only [Zigzag.comp_app, hs, ht, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

lemma forwardBackwardPreimage_joint {S T : forwardBackwardSource W w X Y}
    (h : (forwardBackwardFunctor W w X Y).obj S ⟶ (forwardBackwardFunctor W w X Y).obj T) :
    TwoSidedGrothendieck.baseMap ((forwardBackwardFunctor W w X Y).map
      (forwardBackwardPreimage W w X Y h)) = TwoSidedGrothendieck.baseMap h := by
  apply WideSubcategory.hom_ext
  exact eq_of_heq ((forwardBackwardPreimage_app W w X Y h _).trans
    (forwardBackwardRebuildMap_joint W w X Y h))

lemma forwardBackwardPreimage_tail {S T : forwardBackwardSource W w X Y}
    (h : (forwardBackwardFunctor W w X Y).obj S ⟶ (forwardBackwardFunctor W w X Y).obj T)
    (j : Fin (Word.cons .backward w).length) :
    (TwoSidedGrothendieck.rightMap ((forwardBackwardFunctor W w X Y).map
      (forwardBackwardPreimage W w X Y h))).2.app j.succ =
        (TwoSidedGrothendieck.rightMap h).2.app j.succ := by
  exact eq_of_heq ((forwardBackwardPreimage_app W w X Y h _).trans
    (forwardBackwardRebuildMap_tail W w X Y h j.succ))

end SerrePositivity.EInfinity.Hammock.FirstColumn
