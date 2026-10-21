module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardObjects

/-!
# 元の forward・backward の切断関手の恒等・合成

概要：元の接合点と全縦射を持つ混合二方向の分解。
方針：通常 Hom と残りの backward 語を同じ共変係数の積にする。
規約：元の指定射・全対象・全射を保持する。
使われ方：DK9.4・10.3の全語の帰納。
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
lemma forwardBackwardMap_id (S : forwardBackwardSource W w X Y) :
    forwardBackwardMap W w X Y (𝟙 S) = 𝟙 (forwardBackwardObject W w X Y S) := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · exact CoefficientProduct.pointHom_heq _ _
  · refine HEq.trans ?_ (TwoSidedGrothendieck.rightMap_id_heq _).symm
    refine CoefficientProduct.pair_heq (discreteHom_heq_id_cod _) ?_
    change HEq (backwardMovingToHom _ (ZigzagAppend.Part.rightBoundaryHom (𝟙 S)))
      (𝟙 (ZigzagAppend.Part.rightObj S))
    refine Zigzag.hom_hext (backward_id_obj (ZigzagAppend.Part.rightObj S)) rfl _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero => exact eqToHom_heq_id_cod _ _ (ZigzagAppend.Part.rightObj S).first.symm
    | succ j => rfl
lemma forwardBackwardMap_comp {S T U : forwardBackwardSource W w X Y} (h : S ⟶ T) (k : T ⟶ U) :
    forwardBackwardMap W w X Y (h ≫ k) =
      forwardBackwardMap W w X Y h ≫ forwardBackwardMap W w X Y k := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · exact CoefficientProduct.pointHom_heq _ _
  · refine HEq.trans ?_ (TwoSidedGrothendieck.rightMap_comp_heq _ _).symm
    refine CoefficientProduct.pair_heq ?_ ?_
    · exact (discreteHom_heq_id_cod _).trans (discreteHom_heq_id_cod _).symm
    · change HEq (backwardMovingToHom _ (ZigzagAppend.Part.rightBoundaryHom (h ≫ k)))
        ((backwardFunctor (forwardBackwardBase W w X Y k).hom
          (forwardBackwardBase W w X Y k).property).map
            (backwardMovingToHom _ (ZigzagAppend.Part.rightBoundaryHom h)) ≫
              backwardMovingToHom _ (ZigzagAppend.Part.rightBoundaryHom k))
      refine Zigzag.hom_hext (backward_comp_obj (ZigzagAppend.Part.rightObj S)
        (forwardBackwardBase W w X Y h).hom (forwardBackwardBase W w X Y h).property
        (forwardBackwardBase W w X Y k).hom
        (forwardBackwardBase W w X Y k).property).symm rfl _ _ ?_
      intro j
      cases j using Fin.cases with
      | zero =>
        change HEq (eqToHom (ZigzagAppend.Part.rightObj U).first.symm)
          ((𝟙 _) ≫ eqToHom (ZigzagAppend.Part.rightObj U).first.symm)
        simp only [Category.id_comp]
        rfl
      | succ j => rfl

def forwardBackwardFunctor : forwardBackwardSource W w X Y ⥤ forwardBackwardTarget W w X Y where
  obj := forwardBackwardObject W w X Y
  map := forwardBackwardMap W w X Y
  map_id := forwardBackwardMap_id W w X Y
  map_comp := forwardBackwardMap_comp W w X Y
end SerrePositivity.EInfinity.Hammock.FirstColumn
