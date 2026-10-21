module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardObjects

/-!
# 元の前向きの切断から二方向 Grothendieck 圏への関手

概要：先頭の一列と残りの元の語を接合点で切り出す。
方針：底の指定射・残りの全縦射・先頭列の Hom を保持する。
規約：元の対象と全縦射を使う。圏同値と他の向きは後続。
使われ方：DK9.4・10.3の全語の分解。
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

lemma forwardForwardMap_id (S : forwardForwardSource W w X Y) :
    forwardForwardMap W w X Y (𝟙 S) = 𝟙 (forwardForwardObject W w X Y S) := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · refine HEq.trans ?_ (TwoSidedGrothendieck.leftMap_id_heq _).symm
    change HEq (forwardMovingToHom (forwardForwardBoundary W w X Y (𝟙 S)))
      (𝟙 (ZigzagAppend.Part.rightObj S))
    refine Zigzag.hom_hext rfl (forward_id_obj (ZigzagAppend.Part.rightObj S)) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero => exact eqToHom_heq_id_dom _ _ (ZigzagAppend.Part.rightObj S).first
    | succ j => rfl
  · exact (discreteHom_heq_id_cod _).trans
      (TwoSidedGrothendieck.rightMap_id_heq _).symm

lemma forwardForwardMap_comp {S T U : forwardForwardSource W w X Y} (h : S ⟶ T) (k : T ⟶ U) :
    forwardForwardMap W w X Y (h ≫ k) =
      forwardForwardMap W w X Y h ≫ forwardForwardMap W w X Y k := by
  apply TwoSidedGrothendieck.hom_ext_heq
  · rfl
  · refine HEq.trans ?_ (TwoSidedGrothendieck.leftMap_comp_heq _ _).symm
    change HEq (forwardMovingToHom (forwardForwardBoundary W w X Y (h ≫ k)))
      (forwardMovingToHom (forwardForwardBoundary W w X Y h) ≫
        (forwardFunctor (forwardForwardBase W w X Y h).hom).map
          (forwardMovingToHom (forwardForwardBoundary W w X Y k)))
    refine Zigzag.hom_hext rfl (forward_comp_obj (ZigzagAppend.Part.rightObj U)
      (forwardForwardBase W w X Y k).hom (forwardForwardBase W w X Y h).hom).symm _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      change HEq (eqToHom (ZigzagAppend.Part.rightObj S).first)
        (eqToHom (ZigzagAppend.Part.rightObj S).first ≫ 𝟙 _)
      simp only [Category.comp_id]
      rfl
    | succ j => rfl
  · exact (discreteHom_heq_id_cod _).trans (discreteHom_heq_id_cod _).symm

def forwardForwardFunctor : forwardForwardSource W w X Y ⥤ forwardForwardTarget W w X Y where
  obj := forwardForwardObject W w X Y
  map := forwardForwardMap W w X Y
  map_id := forwardForwardMap_id W w X Y
  map_comp := forwardForwardMap_comp W w X Y

end SerrePositivity.EInfinity.Hammock.FirstColumn
