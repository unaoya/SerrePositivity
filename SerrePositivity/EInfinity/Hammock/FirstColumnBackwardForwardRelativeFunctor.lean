module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardForwardRelativeObject

/-!
# 元の混合二方向の全射の相対自然性

概要：元の係数積と全相対作用素を保持する。
方針：両係数の元の写像と切断の全成分を組にする。
規約：同じ元の graph と augmentation を使う。
使われ方：DK10.3の混合二方向の自然な分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization Zigzag.FirstBoundary
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

variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma backwardForward_relative_map {S T : backwardForwardSource C.weakEquivalences w X Y}
    (h : S ⟶ T) : HEq
    ((backwardForwardFunctor D.weakEquivalences w X' Y').map
      ((Zigzag.Relative.fixedFunctor F hX hY).map h))
    ((backwardForwardRelativeFunctor w F hX hY).map
      ((backwardForwardFunctor C.weakEquivalences w X Y).map h)) := by
  refine hom_hext_components (backwardForward_relative_obj w F hX hY S)
    (backwardForward_relative_obj w F hX hY T) _ _ ?_ ?_ ?_
  · rfl
  · refine HEq.trans ?_ (TwoSidedGrothendieck.coefficientMap_leftMap_heq
      (backwardForwardDataMap w F hX hY).left
      (backwardForwardDataMap w F hX hY).right
      ((backwardForwardFunctor C.weakEquivalences w X Y).map h)).symm
    refine CoefficientProduct.pair_heq ?_ ?_
    · exact discreteHom_heq _ _ (backwardForward_relative_head w F hX hY S)
    · refine Zigzag.hom_hext (ZigzagAppend.Part.right_relative_obj F hX hY S)
        ((congrArg (fun U => forward U (F.functor.map
          (backwardForwardBase C.weakEquivalences w X Y h).hom))
          (ZigzagAppend.Part.right_relative_obj F hX hY T)).trans
          (forward_relative_obj F hY (ZigzagAppend.Part.rightObj T)
            (backwardForwardBase C.weakEquivalences w X Y h).hom).symm) _ _ ?_
      intro j
      cases j using Fin.cases with
      | zero =>
        change HEq (eqToHom (ZigzagAppend.Part.rightObj
          ((Zigzag.Relative.fixedFunctor F hX hY).obj S)).first)
          (F.functor.map (eqToHom (ZigzagAppend.Part.rightObj S).first))
        simp only [eqToHom_map]
        rfl
      | succ j => rfl
  · exact CoefficientProduct.pointHom_heq _ _
lemma backwardForward_relative_functor :
    Zigzag.Relative.fixedFunctor F hX hY ⋙ backwardForwardFunctor D.weakEquivalences w X' Y' =
      backwardForwardFunctor C.weakEquivalences w X Y ⋙
        backwardForwardRelativeFunctor w F hX hY := by
  refine CategoryTheory.Functor.hext (backwardForward_relative_obj w F hX hY) ?_
  intro S T h
  exact backwardForward_relative_map w F hX hY h
end SerrePositivity.EInfinity.Hammock.FirstColumn
