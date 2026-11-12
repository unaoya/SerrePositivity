module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardBackwardObjects

/-!
# 元の forward・backward の切断関手の恒等・合成

概要：元の接合点と全縦射を持つ混合二方向の分解。
方針：通常 Hom と残りの backward 語を同じ共変係数の積にする。
規約：元の指定射・全対象・全射を保持する。
使われ方：DK9.4・10.3の全語の帰納。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
private lemma discreteHom_heq_id_cod {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 y) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)
lemma forwardBackwardMap_id (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardMap W w X Y (𝟙 S) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardObject W w X Y S) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.pointHom_heq _ _
  · refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.rightMap_id_heq _).symm
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.pair_heq (discreteHom_heq_id_cod _) ?_
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardMovingToHom _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBoundaryHom (𝟙 S)))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S))
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_id_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S)) rfl _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero => exact eqToHom_heq_id_cod _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S).first.symm
    | succ j => rfl
lemma forwardBackwardMap_comp {S T U : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y} (h : S ⟶ T) (k : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardMap W w X Y (h ≫ k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardMap W w X Y h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardMap W w X Y k := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.pointHom_heq _ _
  · refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.rightMap_comp_heq _ _).symm
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.pair_heq ?_ ?_
    · exact (discreteHom_heq_id_cod _).trans (discreteHom_heq_id_cod _).symm
    · change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardMovingToHom _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBoundaryHom (h ≫ k)))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardBase W w X Y k).hom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardBase W w X Y k).property).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardMovingToHom _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBoundaryHom h)) ≫
              _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardMovingToHom _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBoundaryHom k))
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_comp_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardBase W w X Y h).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardBase W w X Y h).property
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardBase W w X Y k).hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardBase W w X Y k).property).symm rfl _ _ ?_
      intro j
      cases j using Fin.cases with
      | zero =>
        change HEq (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj U).first.symm)
          ((𝟙 _) ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj U).first.symm)
        simp only [Category.id_comp]
        rfl
      | succ j => rfl

def forwardBackwardFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardSource W w X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardTarget W w X Y where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardObject W w X Y
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardMap W w X Y
  map_id := forwardBackwardMap_id W w X Y
  map_comp := forwardBackwardMap_comp W w X Y
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
