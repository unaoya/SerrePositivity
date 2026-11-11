module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendAssociativity
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 固定語の graph の元の合成の結合則

概要：三つの固定語の元の合成は、語の結合遷移の後で結合的。
方針：全単体の全対象・全縦射を三重連結の照合で比較する。
規約：元の全次数を保持し、π₀ の比較で代用しない。
使われ方：実際の全語の余極限上の合成の結合則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z V : C)

lemma graphComposition_assoc :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a b X Y Z ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W c Z V)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c X Z V ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X V).map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_assoc a b c)) =
      (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b Y Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W c Z V)).hom ≫
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W b c Y Z V) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c) X Y V := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram_map]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change (p.1.1.prod' p.1.2 ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor).prod' p.2 ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_assoc a b c)) =
    p.1.1.prod' (p.1.2.prod' p.2 ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor
  apply Functor.hext (fun j => eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_eqToHom_heq _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_assoc_heq (p.1.1.obj j) (p.1.2.obj j) (p.2.obj j))))
  intro i j f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.map_eqToHom_heq _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendAssociativity.map_assoc_heq (p.1.1.map f) (p.1.2.map f) (p.2.map f))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
