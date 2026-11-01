module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardPreimage

/-!
# 元の前向き二列の Grothendieck 分解の圏同値

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
private lemma discreteHom_heq_id_cod {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 y) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)

lemma forwardForwardPreimage_map {S T : forwardForwardSource W w X Y}
    (h : (forwardForwardFunctor W w X Y).obj S ⟶ (forwardForwardFunctor W w X Y).obj T) :
    (forwardForwardFunctor W w X Y).map (forwardForwardPreimage W w X Y h) = h := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · exact forwardForwardPreimage_joint W w X Y h
  · refine Zigzag.hom_hext rfl
      (congrArg (fun f => forward (ZigzagAppend.Part.rightObj T) f.hom)
        (forwardForwardPreimage_joint W w X Y h)) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      exact (heq_of_eq (TwoSidedGrothendieck.leftMap
        ((forwardForwardFunctor W w X Y).map (forwardForwardPreimage W w X Y h))).first).trans
          (heq_of_eq (TwoSidedGrothendieck.leftMap h).first).symm
    | succ j => exact heq_of_eq (forwardForwardPreimage_tail W w X Y h j)
  · exact (discreteHom_heq_id_cod _).trans (discreteHom_heq_id_cod _).symm

instance forwardForwardFunctor_full : (forwardForwardFunctor W w X Y).Full where
  map_surjective h := ⟨forwardForwardPreimage W w X Y h, forwardForwardPreimage_map W w X Y h⟩

instance forwardForwardFunctor_isEquivalence :
    (forwardForwardFunctor W w X Y).IsEquivalence where

def forwardForwardEquivalence : forwardForwardSource W w X Y ≌ forwardForwardTarget W w X Y :=
  (forwardForwardFunctor W w X Y).asEquivalence
end SerrePositivity.EInfinity.Hammock.FirstColumn
