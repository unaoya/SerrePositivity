module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumnBackwardBackwardRelativeObject

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.Opposite
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
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

lemma backwardBackward_relative_map {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource C.weakEquivalences w X Y}
    (h : S ⟶ T) : HEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor D.weakEquivalences w X' Y').map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).map h))
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackwardRelativeFunctor w F hX hY).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor C.weakEquivalences w X Y).map h)) := by
  refine _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.hom_hext_components (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackward_relative_obj w F hX hY S)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackward_relative_obj w F hX hY T) _ _ ?_ ?_ ?_
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.discreteHom_heq _ _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackward_relative_head w F hX hY S)
  · refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coefficientMap_rightMap_heq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardLeftMap (Y := Y) (Y' := Y') w F hX)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardRightMap (X := X) (X' := X') w F hY)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor C.weakEquivalences w X Y).map h)).symm
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext
      ((congrArg (fun U => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward U
        (F.functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardBase C.weakEquivalences w X Y h).hom)
        (F.map _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardBase C.weakEquivalences w X Y h).property))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY S)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_relative_obj F hY (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardBase C.weakEquivalences w X Y h).hom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardBase C.weakEquivalences w X Y h).property).symm)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.right_relative_obj F hX hY T) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      change HEq (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj T)).first.symm)
        (F.functor.map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj T).first.symm))
      simp only [eqToHom_map]
      rfl
    | succ j => rfl
lemma backwardBackward_relative_functor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor D.weakEquivalences w X' Y' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor C.weakEquivalences w X Y ⋙
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackwardRelativeFunctor w F hX hY := by
  refine CategoryTheory.Functor.hext (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackward_relative_obj w F hX hY) ?_
  intro S T h
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.backwardBackward_relative_map w F hX hY h
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
