module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardRelativeObject

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
private lemma discreteHom_heq_id_cod {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 y) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)
private lemma discreteHom_heq {A : Type u} {x y x' y' : Discrete A}
    (f : x ⟶ y) (g : x' ⟶ y') (hy : y = y') : HEq f g := by
  cases hy
  exact (discreteHom_heq_id_cod f).trans (discreteHom_heq_id_cod g).symm
variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma forwardBackward_relative_map {S T : forwardBackwardSource C.weakEquivalences w X Y}
    (h : S ⟶ T) : HEq
    ((forwardBackwardFunctor D.weakEquivalences w X' Y').map
      ((Zigzag.Relative.fixedFunctor F hX hY).map h))
    ((forwardBackwardRelativeFunctor w F hX hY).map
      ((forwardBackwardFunctor C.weakEquivalences w X Y).map h)) := by
  refine hom_hext_components (forwardBackward_relative_obj w F hX hY S)
    (forwardBackward_relative_obj w F hX hY T) _ _ ?_ ?_ ?_
  · rfl
  · exact CoefficientProduct.pointHom_heq _ _
  · refine HEq.trans ?_ (TwoSidedGrothendieck.coefficientMap_rightMap_heq
      (forwardBackwardDataMap w F hX hY).left
      (forwardBackwardDataMap w F hX hY).right
      ((forwardBackwardFunctor C.weakEquivalences w X Y).map h)).symm
    refine CoefficientProduct.pair_heq ?_ ?_
    · exact discreteHom_heq _ _ (forwardBackward_relative_head w F hX hY T)
    · refine Zigzag.hom_hext
        ((congrArg (fun U => backward U
          (F.functor.map (forwardBackwardBase C.weakEquivalences w X Y h).hom)
          (F.map _ (forwardBackwardBase C.weakEquivalences w X Y h).property))
          (ZigzagAppend.Part.right_relative_obj F hX hY S)).trans
          (backward_relative_obj F hY (ZigzagAppend.Part.rightObj S)
            (forwardBackwardBase C.weakEquivalences w X Y h).hom
            (forwardBackwardBase C.weakEquivalences w X Y h).property).symm)
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
lemma forwardBackward_relative_functor :
    Zigzag.Relative.fixedFunctor F hX hY ⋙ forwardBackwardFunctor D.weakEquivalences w X' Y' =
      forwardBackwardFunctor C.weakEquivalences w X Y ⋙
        forwardBackwardRelativeFunctor w F hX hY := by
  refine CategoryTheory.Functor.hext (forwardBackward_relative_obj w F hX hY) ?_
  intro S T h
  exact forwardBackward_relative_map w F hX hY h
end SerrePositivity.EInfinity.Hammock.FirstColumn
