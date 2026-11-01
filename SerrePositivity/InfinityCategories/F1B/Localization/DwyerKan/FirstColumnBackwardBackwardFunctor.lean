module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardBackwardObjects

/-!
# 元の後向き二列から二方向 Grothendieck 圏への関手

概要：元の接合点の指定射と両側の全縦成分を保持して切断する。
方針：指定 Hom の反変係数と残りの語の共変係数を使う。
規約：元の指定部分圏と実際の全射を使う。
使われ方：DK9.4・10.3の後向き二列の分解。
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
lemma backwardBackwardMap_id (S : backwardBackwardSource W w X Y) :
    backwardBackwardMap W w X Y (𝟙 S) = 𝟙 (backwardBackwardObject W w X Y S) := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · exact (discreteHom_heq_id_dom _).trans (TwoSidedGrothendieck.leftMap_id_heq _).symm
  · refine HEq.trans ?_ (TwoSidedGrothendieck.rightMap_id_heq _).symm
    change HEq (backwardMovingToHom _ (backwardBackwardBoundary W w X Y (𝟙 S)))
      (𝟙 (ZigzagAppend.Part.rightObj S))
    refine Zigzag.hom_hext (backward_id_obj (ZigzagAppend.Part.rightObj S)) rfl _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero => exact eqToHom_heq_id_cod _ _ (ZigzagAppend.Part.rightObj S).first.symm
    | succ j => rfl
lemma backwardBackwardMap_comp {S T U : backwardBackwardSource W w X Y} (h : S ⟶ T) (k : T ⟶ U) :
    backwardBackwardMap W w X Y (h ≫ k) =
      backwardBackwardMap W w X Y h ≫ backwardBackwardMap W w X Y k := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · exact (discreteHom_heq_id_dom _).trans (discreteHom_heq_id_dom _).symm
  · refine HEq.trans ?_ (TwoSidedGrothendieck.rightMap_comp_heq _ _).symm
    change HEq (backwardMovingToHom _ (backwardBackwardBoundary W w X Y (h ≫ k)))
      ((backwardFunctor (backwardBackwardBase W w X Y k).hom
        (backwardBackwardBase W w X Y k).property).map
          (backwardMovingToHom _ (backwardBackwardBoundary W w X Y h)) ≫
            backwardMovingToHom _ (backwardBackwardBoundary W w X Y k))
    refine Zigzag.hom_hext (backward_comp_obj (ZigzagAppend.Part.rightObj S)
      (backwardBackwardBase W w X Y h).hom (backwardBackwardBase W w X Y h).property
      (backwardBackwardBase W w X Y k).hom
      (backwardBackwardBase W w X Y k).property).symm rfl _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      change HEq (eqToHom (ZigzagAppend.Part.rightObj U).first.symm)
        ((𝟙 _) ≫ eqToHom (ZigzagAppend.Part.rightObj U).first.symm)
      simp only [Category.id_comp]
      rfl
    | succ j => rfl

def backwardBackwardFunctor : backwardBackwardSource W w X Y ⥤ backwardBackwardTarget W w X Y where
  obj := backwardBackwardObject W w X Y
  map := backwardBackwardMap W w X Y
  map_id := backwardBackwardMap_id W w X Y
  map_comp := backwardBackwardMap_comp W w X Y
end SerrePositivity.EInfinity.Hammock.FirstColumn
