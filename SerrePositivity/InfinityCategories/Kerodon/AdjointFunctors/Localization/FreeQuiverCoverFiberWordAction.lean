module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagWordValue

/-!
# 元の全語の作用の値の fiber への制限

概要：元の全語の作用を元の値の等式で定まる全部分圏へ制限する。
方針：既存の値の不変性と元の遷移関手を使う。
規約：被覆を経由する別の語の作用で置き換えない。
使われ方：全語の値の fiber の厳密な圏値図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def zigzagFiberWordAction {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A a Y β ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A b Y β where
  obj S := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S.obj,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_value _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top f S.obj).trans
      S.property⟩
  map g := ObjectProperty.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).map g.hom)
  map_id S := ObjectProperty.hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A _ Y β)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).map_id S.obj)
  map_comp g h := ObjectProperty.hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A _ Y β)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).map_comp g.hom h.hom)

lemma zigzagFiberWordAction_inclusion {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    zigzagFiberWordAction A Y β f ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A b Y β).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A a Y β).ι ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f := by
  apply CategoryTheory.Functor.hext
    (F := zigzagFiberWordAction A Y β f ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A b Y β).ι)
    (G := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A a Y β).ι ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
  · intro S
    rfl
  · intro S T g
    rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
