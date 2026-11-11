module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramPrecomp

/-!
# 一列の全図式と端点表示の変更・再添字

概要：同じ自然変換の異種等式を一列の全図式の異種等式へ移す。
方針：端点関手の等式で帰納し、元の自然変換と全縦射を回収する。
規約：射の指定性の証明の選択に依存しない。
使われ方：prefix と残りの内部接続列の全単体作用素への整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {I : Type uI} [Category.{vI} I]
  {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

lemma diagram_heq {A A' B B' : D ⥤ C} (hA : A = A') (hB : B = B')
    (α : A ⟶ B) (β : A' ⟶ B')
    (mA : ∀ {d e : D} (f : d ⟶ e), W (A.map f))
    (mB : ∀ {d e : D} (f : d ⟶ e), W (B.map f))
    (mA' : ∀ {d e : D} (f : d ⟶ e), W (A'.map f))
    (mB' : ∀ {d e : D} (f : d ⟶ e), W (B'.map f)) (hα : HEq α β) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W α mA mB) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W β mA' mB') := by
  cases hA
  cases hB
  have hα := eq_of_heq hα
  cases hα
  rfl

lemma diagram_precomp {A B : D ⥤ C} (K : I ⥤ D) (α : A ⟶ B)
    (mA : ∀ {d e : D} (f : d ⟶ e), W (A.map f))
    (mB : ∀ {d e : D} (f : d ⟶ e), W (B.map f)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W α mA mB).precomp K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W (Functor.whiskerLeft K α) (fun f => mA (K.map f))
        (fun f => mB (K.map f)) := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
