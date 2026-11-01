module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardForwardObjects

/-!
# 元の backward・forward の切断関手の恒等・合成

概要：元の指定 Hom と残りの語を同じ反変係数の積へ回収する。
方針：元の接合点・全縦成分と貼り戻しの全往復を使う。
規約：元の切断関手自体を保持する。
使われ方：DK9.4・10.3の残る混合二方向の分解。
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
lemma backwardForwardMap_id (S : backwardForwardSource W w X Y) :
    backwardForwardMap W w X Y (𝟙 S) = 𝟙 (backwardForwardObject W w X Y S) := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · refine HEq.trans ?_ (TwoSidedGrothendieck.leftMap_id_heq _).symm
    refine CoefficientProduct.pair_heq (discreteHom_heq_id_dom _) ?_
    change HEq (forwardMovingToHom (ZigzagAppend.Part.rightBoundaryHom (𝟙 S)))
      (𝟙 (ZigzagAppend.Part.rightObj S))
    refine Zigzag.hom_hext rfl (forward_id_obj (ZigzagAppend.Part.rightObj S)) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero => exact eqToHom_heq_id_dom _ _ (ZigzagAppend.Part.rightObj S).first
    | succ j => rfl
  · exact CoefficientProduct.pointHom_heq _ _
lemma backwardForwardMap_comp {S T U : backwardForwardSource W w X Y} (h : S ⟶ T) (k : T ⟶ U) :
    backwardForwardMap W w X Y (h ≫ k) =
      backwardForwardMap W w X Y h ≫ backwardForwardMap W w X Y k := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · refine HEq.trans ?_ (TwoSidedGrothendieck.leftMap_comp_heq _ _).symm
    refine CoefficientProduct.pair_heq ?_ ?_
    · exact (discreteHom_heq_id_dom _).trans (discreteHom_heq_id_dom _).symm
    · change HEq (forwardMovingToHom (ZigzagAppend.Part.rightBoundaryHom (h ≫ k)))
        (forwardMovingToHom (ZigzagAppend.Part.rightBoundaryHom h) ≫
          (forwardFunctor (backwardForwardBase W w X Y h).hom).map
            (forwardMovingToHom (ZigzagAppend.Part.rightBoundaryHom k)))
      refine Zigzag.hom_hext rfl (forward_comp_obj (ZigzagAppend.Part.rightObj U)
        (backwardForwardBase W w X Y k).hom (backwardForwardBase W w X Y h).hom).symm _ _ ?_
      intro j
      cases j using Fin.cases with
      | zero =>
        change HEq (eqToHom (ZigzagAppend.Part.rightObj S).first)
          (eqToHom (ZigzagAppend.Part.rightObj S).first ≫ 𝟙 _)
        simp only [Category.comp_id]
        rfl
      | succ j => rfl
  · exact CoefficientProduct.pointHom_heq _ _
def backwardForwardFunctor : backwardForwardSource W w X Y ⥤ backwardForwardTarget W w X Y where
  obj := backwardForwardObject W w X Y
  map := backwardForwardMap W w X Y
  map_id := backwardForwardMap_id W w X Y
  map_comp := backwardForwardMap_comp W w X Y
end SerrePositivity.EInfinity.Hammock.FirstColumn
