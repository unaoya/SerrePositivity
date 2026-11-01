module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardRebuildMap

/-!
# 元の前向き切断の射の逆像と全成分の回収

概要：元の固定語の全縦射と二方向 Grothendieck 圏の全射を回収する。
方針：接合点と残りの全成分を回収し、元の切断関手の充満性を示す。
規約：元の切断関手自体を使い、モデル構造を要求しない。
使われ方：DK9.4・10.3の元の語の分解。
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
def forwardForwardPreimage {S T : forwardForwardSource W w X Y}
    (h : (forwardForwardFunctor W w X Y).obj S ⟶ (forwardForwardFunctor W w X Y).obj T) : S ⟶ T :=
  eqToHom (forwardForwardRebuild_functor_obj W w X Y S).symm ≫
    forwardForwardRebuildMap W w X Y h ≫ eqToHom (forwardForwardRebuild_functor_obj W w X Y T)

lemma forwardForwardPreimage_app {S T : forwardForwardSource W w X Y}
    (h : (forwardForwardFunctor W w X Y).obj S ⟶ (forwardForwardFunctor W w X Y).obj T)
    (j : Fin ((Word.append (Word.single .forward) (Word.cons .forward w)).length + 1)) :
    HEq ((forwardForwardPreimage W w X Y h).app j)
      ((forwardForwardRebuildMap W w X Y h).app j) := by
  have hs := eqToHom_map (Zigzag.evaluation (W := W) j)
    (forwardForwardRebuild_functor_obj W w X Y S).symm
  have ht := eqToHom_map (Zigzag.evaluation (W := W) j)
    (forwardForwardRebuild_functor_obj W w X Y T)
  dsimp only [Zigzag.evaluation] at hs ht
  dsimp only [forwardForwardPreimage]
  simp only [Zigzag.comp_app, hs, ht, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

lemma forwardForwardPreimage_joint {S T : forwardForwardSource W w X Y}
    (h : (forwardForwardFunctor W w X Y).obj S ⟶ (forwardForwardFunctor W w X Y).obj T) :
    TwoSidedGrothendieck.baseMap ((forwardForwardFunctor W w X Y).map
      (forwardForwardPreimage W w X Y h)) = TwoSidedGrothendieck.baseMap h := by
  apply WideSubcategory.hom_ext
  exact eq_of_heq ((forwardForwardPreimage_app W w X Y h _).trans
    (forwardForwardRebuildMap_joint W w X Y h))

lemma forwardForwardPreimage_tail {S T : forwardForwardSource W w X Y}
    (h : (forwardForwardFunctor W w X Y).obj S ⟶ (forwardForwardFunctor W w X Y).obj T)
    (j : Fin (Word.cons .forward w).length) :
    (TwoSidedGrothendieck.leftMap ((forwardForwardFunctor W w X Y).map
      (forwardForwardPreimage W w X Y h))).app j.succ =
        (TwoSidedGrothendieck.leftMap h).app j.succ := by
  exact eq_of_heq ((forwardForwardPreimage_app W w X Y h _).trans
    (forwardForwardRebuildMap_tail W w X Y h j.succ))

end SerrePositivity.EInfinity.Hammock.FirstColumn
