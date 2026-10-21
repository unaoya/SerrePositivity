module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardRelativeObject

/-!
# 元の後向き二列の切断関手の全射の相対自然性

概要：元の底と両係数を送る相対関手と切断関手を厳密に照合する。
方針：指定 Hom の反変作用と残りの語の共変作用の全成分を回収する。
規約：元の両端の等式移送と全縦射を保持する。
使われ方：DK10.3の後向き二列の単体図式への分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary SimplicialLocalization
variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
private lemma hom_hext_components {B : Type u} [Category.{u} B]
    {P : Bᵒᵖ ⥤ Cat.{u, u}} {Q : B ⥤ Cat.{u, u}}
    {S T S' T' : TwoSidedGrothendieck.total P Q} (hS : S = S') (hT : T = T')
    (f : S ⟶ T) (g : S' ⟶ T')
    (hb : HEq (TwoSidedGrothendieck.baseMap f) (TwoSidedGrothendieck.baseMap g))
    (hl : HEq (TwoSidedGrothendieck.leftMap f) (TwoSidedGrothendieck.leftMap g))
    (hr : HEq (TwoSidedGrothendieck.rightMap f) (TwoSidedGrothendieck.rightMap g)) : HEq f g := by
  cases hS
  cases hT
  exact heq_of_eq (TwoSidedGrothendieck.hom_ext_heq f g (eq_of_heq hb) hl hr)
private lemma discreteHom_heq_id_dom {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 x) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)
private lemma discreteHom_heq {A : Type u} {x y x' y' : Discrete A}
    (f : x ⟶ y) (g : x' ⟶ y') (hx : x = x') : HEq f g := by
  cases hx
  exact (discreteHom_heq_id_dom f).trans (discreteHom_heq_id_dom g).symm

lemma backwardBackward_relative_map {S T : backwardBackwardSource C.weakEquivalences w X Y}
    (h : S ⟶ T) : HEq
    ((backwardBackwardFunctor D.weakEquivalences w X' Y').map
      ((Zigzag.Relative.fixedFunctor F hX hY).map h))
    ((backwardBackwardRelativeFunctor w F hX hY).map
      ((backwardBackwardFunctor C.weakEquivalences w X Y).map h)) := by
  refine hom_hext_components (backwardBackward_relative_obj w F hX hY S)
    (backwardBackward_relative_obj w F hX hY T) _ _ ?_ ?_ ?_
  · rfl
  · exact discreteHom_heq _ _ (backwardBackward_relative_head w F hX hY S)
  · refine HEq.trans ?_ (TwoSidedGrothendieck.coefficientMap_rightMap_heq
      (backwardBackwardLeftMap (Y := Y) (Y' := Y') w F hX)
      (backwardBackwardRightMap (X := X) (X' := X') w F hY)
      ((backwardBackwardFunctor C.weakEquivalences w X Y).map h)).symm
    refine Zigzag.hom_hext
      ((congrArg (fun U => backward U
        (F.functor.map (backwardBackwardBase C.weakEquivalences w X Y h).hom)
        (F.map _ (backwardBackwardBase C.weakEquivalences w X Y h).property))
        (ZigzagAppend.Part.right_relative_obj F hX hY S)).trans
        (backward_relative_obj F hY (ZigzagAppend.Part.rightObj S)
          (backwardBackwardBase C.weakEquivalences w X Y h).hom
          (backwardBackwardBase C.weakEquivalences w X Y h).property).symm)
      (ZigzagAppend.Part.right_relative_obj F hX hY T) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      change HEq (eqToHom (ZigzagAppend.Part.rightObj
        ((Zigzag.Relative.fixedFunctor F hX hY).obj T)).first.symm)
        (F.functor.map (eqToHom (ZigzagAppend.Part.rightObj T).first.symm))
      simp only [eqToHom_map]
      rfl
    | succ j => rfl
lemma backwardBackward_relative_functor :
    Zigzag.Relative.fixedFunctor F hX hY ⋙ backwardBackwardFunctor D.weakEquivalences w X' Y' =
      backwardBackwardFunctor C.weakEquivalences w X Y ⋙
        backwardBackwardRelativeFunctor w F hX hY := by
  refine CategoryTheory.Functor.hext (backwardBackward_relative_obj w F hX hY) ?_
  intro S T h
  exact backwardBackward_relative_map w F hX hY h
end SerrePositivity.EInfinity.Hammock.FirstColumn
