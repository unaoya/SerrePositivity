module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardPreimage

/-!
# 元の後向き二列の Grothendieck 分解の圏同値

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
private lemma discreteHom_heq_id_dom {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 x) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)
lemma backwardBackwardPreimage_map {S T : backwardBackwardSource W w X Y}
    (h : (backwardBackwardFunctor W w X Y).obj S ⟶ (backwardBackwardFunctor W w X Y).obj T) :
    (backwardBackwardFunctor W w X Y).map (backwardBackwardPreimage W w X Y h) = h := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · exact backwardBackwardPreimage_joint W w X Y h
  · exact (discreteHom_heq_id_dom _).trans (discreteHom_heq_id_dom _).symm
  · refine Zigzag.hom_hext
      (congrArg (fun f => backward (ZigzagAppend.Part.rightObj S) f.hom f.property)
        (backwardBackwardPreimage_joint W w X Y h)) rfl _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      exact (heq_of_eq (TwoSidedGrothendieck.rightMap
        ((backwardBackwardFunctor W w X Y).map (backwardBackwardPreimage W w X Y h))).first).trans
          (heq_of_eq (TwoSidedGrothendieck.rightMap h).first).symm
    | succ j => exact heq_of_eq (backwardBackwardPreimage_tail W w X Y h j)
instance backwardBackwardFunctor_full : (backwardBackwardFunctor W w X Y).Full where
  map_surjective h := ⟨backwardBackwardPreimage W w X Y h, backwardBackwardPreimage_map W w X Y h⟩
instance backwardBackwardFunctor_isEquivalence :
    (backwardBackwardFunctor W w X Y).IsEquivalence where

def backwardBackwardEquivalence : backwardBackwardSource W w X Y ≌ backwardBackwardTarget W w X Y :=
  (backwardBackwardFunctor W w X Y).asEquivalence
end SerrePositivity.EInfinity.Hammock.FirstColumn
