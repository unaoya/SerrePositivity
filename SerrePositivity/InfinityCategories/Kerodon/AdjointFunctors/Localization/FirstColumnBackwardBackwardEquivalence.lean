module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardPreimage

/-!
# 元の後向き二列の Grothendieck 分解の圏同値

概要：元の指定 Hom と残りの全縦射から同じ元の射を回収する。
方針：接合点と全成分の回収で元の切断関手の充満性を示す。
規約：元の切断関手自体と指定部分圏の全射を保持する。
使われ方：DK9.4・10.3の元の後向き二列の分解。

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
private lemma discreteHom_heq_id_dom {A : Type u} {x y : Discrete A} (h : x ⟶ y) :
    HEq h (𝟙 x) := by
  have he : x = y := Discrete.ext (Discrete.eq_of_hom h)
  cases he
  exact heq_of_eq (Subsingleton.elim _ _)
lemma backwardBackwardPreimage_map {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource W w X Y}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).obj S ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).obj T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardPreimage W w X Y h) = h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.hom_ext_heq
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardPreimage_joint W w X Y h
  · exact (discreteHom_heq_id_dom _).trans (discreteHom_heq_id_dom _).symm
  · refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext
      (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S) f.hom f.property)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardPreimage_joint W w X Y h)) rfl _ _ ?_
    intro j
    cases j using Fin.cases with
    | zero =>
      exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardPreimage W w X Y h))).first).trans
          (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap h).first).symm
    | succ j => exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardPreimage_tail W w X Y h j)
instance backwardBackwardFunctor_full : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).Full where
  map_surjective h := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardPreimage W w X Y h, backwardBackwardPreimage_map W w X Y h⟩
instance backwardBackwardFunctor_isEquivalence :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).IsEquivalence where

def backwardBackwardEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource W w X Y ≌ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).asEquivalence
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
