module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardRelativeObject

/-!
# 元の前向き二列の全射の相対自然性

概要：元の切断関手と相対関手の全対象・全射の正方形が厳密に可換である。
方針：元の底・残りの全縦成分・先頭 Hom を同じ二方向図式の関手へ回収する。
規約：両端の表示等式と全ての元の射を保持する。
使われ方：DK9.4・10.3の単体図式への自然な分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary SimplicialLocalization
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
lemma forwardForward_relative_head (S : forwardForwardSource C.weakEquivalences w X Y) :
    Discrete.mk (ForwardZigzag.value (ZigzagAppend.Part.leftObj
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S))) =
    Discrete.mk (eqToHom hX.symm ≫ F.functor.map
      (ForwardZigzag.value (ZigzagAppend.Part.leftObj S))) := by
  apply Discrete.ext
  rw [ZigzagAppend.Part.left_relative_obj F hX hY S]
  simpa only [eqToHom_refl, Category.comp_id] using
    ForwardZigzag.value_relative F hX rfl (ZigzagAppend.Part.leftObj S)

lemma forwardForward_relative_map {S T : forwardForwardSource C.weakEquivalences w X Y}
    (h : S ⟶ T) : HEq
    ((forwardForwardFunctor D.weakEquivalences w X' Y').map
      ((Zigzag.Relative.fixedFunctor F hX hY).map h))
    ((forwardForwardRelativeFunctor w F hX hY).map
      ((forwardForwardFunctor C.weakEquivalences w X Y).map h)) := by
  refine hom_hext_components (forwardForward_relative_obj w F hX hY S)
    (forwardForward_relative_obj w F hX hY T) _ _ ?_ ?_ ?_
  · rfl
  · refine HEq.trans ?_ (TwoSidedGrothendieck.coefficientMap_leftMap_heq
      (forwardForwardLeftMap (X := X) (X' := X') w F hY)
      (forwardForwardRightMap (Y := Y) (Y' := Y') w F hX)
      ((forwardForwardFunctor C.weakEquivalences w X Y).map h)).symm
    refine Zigzag.hom_hext (ZigzagAppend.Part.right_relative_obj F hX hY S)
      ((congrArg (fun U => forward U (F.functor.map
        (forwardForwardBase C.weakEquivalences w X Y h).hom))
        (ZigzagAppend.Part.right_relative_obj F hX hY T)).trans
        (forward_relative_obj F hY (ZigzagAppend.Part.rightObj T)
          (forwardForwardBase C.weakEquivalences w X Y h).hom).symm) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      change HEq (eqToHom (ZigzagAppend.Part.rightObj
        ((Zigzag.Relative.fixedFunctor F hX hY).obj S)).first)
        (F.functor.map (eqToHom (ZigzagAppend.Part.rightObj S).first))
      simp only [eqToHom_map]
      rfl
    | succ j => rfl
  · exact discreteHom_heq _ _ (forwardForward_relative_head w F hX hY T)

lemma forwardForward_relative_functor :
    Zigzag.Relative.fixedFunctor F hX hY ⋙ forwardForwardFunctor D.weakEquivalences w X' Y' =
      forwardForwardFunctor C.weakEquivalences w X Y ⋙ forwardForwardRelativeFunctor w F hX hY := by
  refine CategoryTheory.Functor.hext (forwardForward_relative_obj w F hX hY) ?_
  intro S T h
  exact forwardForward_relative_map w F hX hY h
end SerrePositivity.EInfinity.Hammock.FirstColumn
