module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardObjects

/-!
# 元の前向きの切断から二方向 Grothendieck 圏への関手

概要：先頭の一列と残りの元の語を接合点で切り出す。
方針：底の指定射・残りの全縦射・先頭列の Hom を保持する。
規約：元の対象と全縦射を使う。圏同値と他の向きは後続。
使われ方：DK9.4・10.3の全語の分解。

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

lemma forwardForwardMap_id (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardMap W w X Y (𝟙 S) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y S) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq
  · rfl
  · refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.leftMap_id_heq _).symm
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMovingToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBoundary W w X Y (𝟙 S)))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S))
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_id_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S)) _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero => exact eqToHom_heq_id_dom _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S).first
    | succ j => rfl
  · exact (discreteHom_heq_id_cod _).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.rightMap_id_heq _).symm

lemma forwardForwardMap_comp {S T U : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource W w X Y} (h : S ⟶ T) (k : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardMap W w X Y (h ≫ k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardMap W w X Y h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardMap W w X Y k := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq
  · rfl
  · refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.leftMap_comp_heq _ _).symm
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMovingToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBoundary W w X Y (h ≫ k)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMovingToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBoundary W w X Y h) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBase W w X Y h).hom).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMovingToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBoundary W w X Y k)))
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_comp_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj U)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBase W w X Y k).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardBase W w X Y h).hom).symm _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      change HEq (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S).first)
        (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S).first ≫ 𝟙 _)
      simp only [Category.comp_id]
      rfl
    | succ j => rfl
  · exact (discreteHom_heq_id_cod _).trans (discreteHom_heq_id_cod _).symm

def forwardForwardFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource W w X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardMap W w X Y
  map_id := forwardForwardMap_id W w X Y
  map_comp := forwardForwardMap_comp W w X Y

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
