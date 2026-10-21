module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardRebuildMap

/-!
# 元の後向き切断の全射の逆像と成分の回収

概要：元の指定 Hom と残りの全縦射から同じ元の射を回収する。
方針：接合点と全成分の回収で元の切断関手の充満性を示す。
規約：元の切断関手自体と指定部分圏の全射を保持する。
使われ方：DK9.4・10.3の元の後向き二列の分解。
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
def backwardBackwardPreimage {S T : backwardBackwardSource W w X Y}
    (h : (backwardBackwardFunctor W w X Y).obj S ⟶
      (backwardBackwardFunctor W w X Y).obj T) : S ⟶ T :=
  eqToHom (backwardBackwardRebuild_functor_obj W w X Y S).symm ≫
    backwardBackwardRebuildMap W w X Y h ≫ eqToHom (backwardBackwardRebuild_functor_obj W w X Y T)

lemma backwardBackwardPreimage_app {S T : backwardBackwardSource W w X Y}
    (h : (backwardBackwardFunctor W w X Y).obj S ⟶ (backwardBackwardFunctor W w X Y).obj T)
    (j : Fin ((Word.append (Word.single .backward) (Word.cons .backward w)).length + 1)) :
    HEq ((backwardBackwardPreimage W w X Y h).app j)
      ((backwardBackwardRebuildMap W w X Y h).app j) := by
  have hs := eqToHom_map (Zigzag.evaluation (W := W) j)
    (backwardBackwardRebuild_functor_obj W w X Y S).symm
  have ht := eqToHom_map (Zigzag.evaluation (W := W) j)
    (backwardBackwardRebuild_functor_obj W w X Y T)
  dsimp only [Zigzag.evaluation] at hs ht
  dsimp only [backwardBackwardPreimage]
  simp only [Zigzag.comp_app, hs, ht, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

lemma backwardBackwardPreimage_joint {S T : backwardBackwardSource W w X Y}
    (h : (backwardBackwardFunctor W w X Y).obj S ⟶ (backwardBackwardFunctor W w X Y).obj T) :
    TwoSidedGrothendieck.baseMap ((backwardBackwardFunctor W w X Y).map
      (backwardBackwardPreimage W w X Y h)) = TwoSidedGrothendieck.baseMap h := by
  apply WideSubcategory.hom_ext
  exact eq_of_heq ((backwardBackwardPreimage_app W w X Y h _).trans
    (backwardBackwardRebuildMap_joint W w X Y h))

lemma backwardBackwardPreimage_tail {S T : backwardBackwardSource W w X Y}
    (h : (backwardBackwardFunctor W w X Y).obj S ⟶ (backwardBackwardFunctor W w X Y).obj T)
    (j : Fin (Word.cons .backward w).length) :
    (TwoSidedGrothendieck.rightMap ((backwardBackwardFunctor W w X Y).map
      (backwardBackwardPreimage W w X Y h))).app j.succ =
        (TwoSidedGrothendieck.rightMap h).app j.succ := by
  exact eq_of_heq ((backwardBackwardPreimage_app W w X Y h _).trans
    (backwardBackwardRebuildMap_tail W w X Y h j.succ))

end SerrePositivity.EInfinity.Hammock.FirstColumn
