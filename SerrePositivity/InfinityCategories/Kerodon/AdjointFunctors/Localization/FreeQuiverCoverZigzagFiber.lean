module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagHorizontal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# 元の全指定 zigzag の値を固定した全部分圏

概要：元の自由 groupoid の射を値とする zigzag を全縦射を含めて扱う。
方針：既存の元の値の等式による全部分圏とし、終点ラベルを回収する。
規約：値の等式だけで制限し、元の列や縦射は変更しない。
使われ方：固定端点の被覆上の zigzag への持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def zigzagValueProperty :
    ObjectProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :=
  fun S => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S = β

abbrev ZigzagValueFiber := (zigzagValueProperty A w Y β).FullSubcategory

def fiberEndpoint : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A := ⟨Y, β⟩

variable {w Y β}

lemma zigzagPrefix_last_heq_value
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S (Fin.last w.length))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S (Fin.last w.length) ≫
      eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj S.last) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S :=
    Category.assoc _ _ _
  exact (comp_eqToHom_heq _ _).symm.trans (heq_of_eq he)

lemma zigzagVertex_last (S : ZigzagValueFiber A w Y β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A S.obj (Fin.last w.length) = fiberEndpoint A Y β := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Vertex.ext S.obj.last
  exact (zigzagPrefix_last_heq_value A S.obj).trans (heq_of_eq S.property)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
