module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardForwardPreimage

/-!
# 元の混合二方向 −+の Grothendieck 分解の圏同値

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
private lemma discreteHom_heq_id_dom {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 x) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)

lemma backwardForwardPreimage_map {S T : backwardForwardSource W w X Y}
    (h : (backwardForwardFunctor W w X Y).obj S ⟶ (backwardForwardFunctor W w X Y).obj T) :
    (backwardForwardFunctor W w X Y).map (backwardForwardPreimage W w X Y h) = h := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · exact backwardForwardPreimage_joint W w X Y h
  · refine CoefficientProduct.pair_heq ?_ ?_
    · exact (discreteHom_heq_id_dom _).trans (discreteHom_heq_id_dom _).symm
    · refine Zigzag.hom_hext rfl
        (congrArg (fun f => forward (ZigzagAppend.Part.rightObj T) f.hom)
          (backwardForwardPreimage_joint W w X Y h)) _ _ ?_
      intro j
      cases j using Fin.cases with
      | zero =>
        exact (heq_of_eq (TwoSidedGrothendieck.leftMap
          ((backwardForwardFunctor W w X Y).map (backwardForwardPreimage W w X Y h))).2.first).trans
            (heq_of_eq (TwoSidedGrothendieck.leftMap h).2.first).symm
      | succ j => exact heq_of_eq (backwardForwardPreimage_tail W w X Y h j)
  · exact CoefficientProduct.pointHom_heq _ _

instance backwardForwardFunctor_full : (backwardForwardFunctor W w X Y).Full where
  map_surjective h := ⟨backwardForwardPreimage W w X Y h, backwardForwardPreimage_map W w X Y h⟩

instance backwardForwardFunctor_isEquivalence :
    (backwardForwardFunctor W w X Y).IsEquivalence where

def backwardForwardEquivalence : backwardForwardSource W w X Y ≌ backwardForwardTarget W w X Y :=
  (backwardForwardFunctor W w X Y).asEquivalence
end SerrePositivity.EInfinity.Hammock.FirstColumn
