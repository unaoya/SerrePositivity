module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramExt
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram

/-!
# 元の三つの自然変換の全図式を圧縮する

概要：三つの一列の全図式の圧縮は、元の合成自然変換の図式に厳密に一致する。
方針：全対象で三列圧縮を回収し、全縦射は両端の元の関手の射へ戻す。
規約：内部の二つの接合点の関手も動く。
使われ方：列内部の因子化の全行・全縦射を保つ回収。

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
  (W : MorphismProperty C) [W.IsMultiplicative] {A B E F : D ⥤ C}
  (α : A ⟶ B) (β : B ⟶ E) (γ : E ⟶ F)
  (hA : ∀ {d e : D} (f : d ⟶ e), W (A.map f))
  (hB : ∀ {d e : D} (f : d ⟶ e), W (B.map f))
  (hE : ∀ {d e : D} (f : d ⟶ e), W (E.map f))
  (hF : ∀ {d e : D} (f : d ⟶ e), W (F.map f))

lemma collapse_diagram :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.collapse
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W α hA hB).append
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W β hB hE)).append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W γ hE hF)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W (α ≫ β ≫ γ) hA hF := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext
  · intro d
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleAppend.collapse_append (α.app d) (β.app d) (γ.app d)
  · intro d e f i
    change Fin 2 at i
    cases i using Fin.cases with
    | zero =>
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq _ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.cut_zero).trans
        ((((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W α hA hB).append
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W β hB hE)).append
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W γ hE hF)).first f)
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq _ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.cut_last).trans
        ((((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W α hA hB).append
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W β hB hE)).append
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W γ hE hF)).last f)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
