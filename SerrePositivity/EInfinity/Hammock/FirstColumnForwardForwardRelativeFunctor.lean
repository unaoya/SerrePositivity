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
open CategoryTheory Opposite
private lemma hom_hext_components {B : Type u} [Category.{u} B]
    {P : Bᵒᵖ ⥤ Cat.{u, u}} {Q : B ⥤ Cat.{u, u}}
    {S T S' T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total P Q} (hS : S = S') (hT : T = T')
    (f : S ⟶ T) (g : S' ⟶ T')
    (hb : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap g))
    (hl : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap g))
    (hr : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap g)) : HEq f g := by
  cases hS
  cases hT
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq f g (eq_of_heq hb) hl hr)
private lemma discreteHom_heq_id_cod {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 y) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)
private lemma discreteHom_heq {A : Type u} {x y x' y' : Discrete A}
    (f : x ⟶ y) (g : x' ⟶ y') (hy : y = y') : HEq f g := by
  cases hy
  exact (discreteHom_heq_id_cod f).trans (discreteHom_heq_id_cod g).symm
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma forwardForward_relative_head (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource C.weakEquivalences w X Y) :
    Discrete.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S))) =
    Discrete.mk (eqToHom hX.symm ≫ F.functor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S))) := by
  apply Discrete.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.left_relative_obj F hX hY S]
  simpa only [eqToHom_refl, Category.comp_id] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_relative F hX rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)

lemma forwardForward_relative_map {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource C.weakEquivalences w X Y}
    (h : S ⟶ T) : HEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor D.weakEquivalences w X' Y').map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).map h))
    ((forwardForwardRelativeFunctor w F hX hY).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor C.weakEquivalences w X Y).map h)) := by
  refine hom_hext_components (forwardForward_relative_obj w F hX hY S)
    (forwardForward_relative_obj w F hX hY T) _ _ ?_ ?_ ?_
  · rfl
  · refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_leftMap_heq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardLeftMap (X := X) (X' := X') w F hY)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardRightMap (Y := Y) (Y' := Y') w F hX)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor C.weakEquivalences w X Y).map h)).symm
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY S)
      ((congrArg (fun U => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward U (F.functor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBase C.weakEquivalences w X Y h).hom))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY T)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_relative_obj F hY (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj T)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBase C.weakEquivalences w X Y h).hom).symm) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      change HEq (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S)).first)
        (F.functor.map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S).first))
      simp only [eqToHom_map]
      rfl
    | succ j => rfl
  · exact discreteHom_heq _ _ (forwardForward_relative_head w F hX hY T)

lemma forwardForward_relative_functor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor D.weakEquivalences w X' Y' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor C.weakEquivalences w X Y ⋙ forwardForwardRelativeFunctor w F hX hY := by
  refine CategoryTheory.Functor.hext (forwardForward_relative_obj w F hX hY) ?_
  intro S T h
  exact forwardForward_relative_map w F hX hY h
end SerrePositivity.EInfinity.Hammock.FirstColumn
