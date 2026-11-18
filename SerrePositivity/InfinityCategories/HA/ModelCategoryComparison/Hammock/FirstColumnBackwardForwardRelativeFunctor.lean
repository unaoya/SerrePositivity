module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumnBackwardForwardRelativeObject

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.Opposite
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
private lemma discreteHom_heq_id_dom {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 x) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)
private lemma discreteHom_heq {A : Type u} {x y x' y' : Discrete A}
    (f : x ⟶ y) (g : x' ⟶ y') (hx : x = x') : HEq f g := by
  cases hx
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.discreteHom_heq_id_dom f).trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.discreteHom_heq_id_dom g).symm

variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma backwardForward_relative_map {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardSource C.weakEquivalences w X Y}
    (h : S ⟶ T) : HEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor D.weakEquivalences w X' Y').map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).map h))
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForwardRelativeFunctor w F hX hY).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor C.weakEquivalences w X Y).map h)) := by
  refine _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.hom_hext_components (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForward_relative_obj w F hX hY S)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForward_relative_obj w F hX hY T) _ _ ?_ ?_ ?_
  · rfl
  · refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_leftMap_heq
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForwardDataMap w F hX hY).left
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForwardDataMap w F hX hY).right
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor C.weakEquivalences w X Y).map h)).symm
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.pair_heq ?_ ?_
    · exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.discreteHom_heq _ _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForward_relative_head w F hX hY S)
    · refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY S)
        ((congrArg (fun U => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward U (F.functor.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardBase C.weakEquivalences w X Y h).hom))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY T)).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_relative_obj F hY (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj T)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardBase C.weakEquivalences w X Y h).hom).symm) _ _ ?_
      intro j
      cases j using Fin.cases with
      | zero =>
        change HEq (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S)).first)
          (F.functor.map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S).first))
        simp only [eqToHom_map]
        rfl
      | succ j => rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.pointHom_heq _ _
lemma backwardForward_relative_functor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor D.weakEquivalences w X' Y' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor C.weakEquivalences w X Y ⋙
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForwardRelativeFunctor w F hX hY := by
  refine CategoryTheory.Functor.hext (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForward_relative_obj w F hX hY) ?_
  intro S T h
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardForward_relative_map w F hX hY h
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
