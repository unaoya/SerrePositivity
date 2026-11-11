module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramExt

/-!
# 元の一列の全図式を同じ自然変換から回収する

概要：元の一列の射との異種等式から、全図式そのものを回収する。
方針：両端の元の関手と全縦射を first・last で照合する。
規約：射だけの一致や局所化後の同型で置き換えない。
使われ方：内部切断を圧縮した列と元の middle の同定。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  (W : MorphismProperty C) [W.IsMultiplicative] {A B : D ⥤ C}

lemma diagram_eq_of_arrow (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) A B)
    (α : A ⟶ B) (hA : ∀ {d e : D} (f : d ⟶ e), W (A.map f))
    (hB : ∀ {d e : D} (f : d ⟶ e), W (B.map f))
    (ha : ∀ d, HEq ((F.obj d).arrow (0 : Fin 1)) (α.app d)) :
    F = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W α hA hB := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext
  · intro d
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
    · intro i
      change Fin 2 at i
      cases i using Fin.cases with
      | zero => exact (F.obj d).first
      | succ i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact (F.obj d).last
    · intro i
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ha d
  · intro d e f i
    change Fin 2 at i
    cases i using Fin.cases with
    | zero => exact F.first f
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact F.last f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
