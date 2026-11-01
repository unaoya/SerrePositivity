module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardTripleAppend
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingWordAction
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramAppend
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramExt
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzagDiagram

/-!
# 元の三つの自然変換の全図式を圧縮する

概要：三つの一列の全図式の圧縮は、元の合成自然変換の図式に厳密に一致する。
方針：全対象で三列圧縮を回収し、全縦射は両端の元の関手の射へ戻す。
規約：内部の二つの接合点の関手も動く。
使われ方：列内部の因子化の全行・全縦射を保つ回収。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardTriple
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  (W : MorphismProperty C) [W.IsMultiplicative] {A B E F : D ⥤ C}
  (α : A ⟶ B) (β : B ⟶ E) (γ : E ⟶ F)
  (hA : ∀ {d e : D} (f : d ⟶ e), W (A.map f))
  (hB : ∀ {d e : D} (f : d ⟶ e), W (B.map f))
  (hE : ∀ {d e : D} (f : d ⟶ e), W (E.map f))
  (hF : ∀ {d e : D} (f : d ⟶ e), W (F.map f))

lemma collapse_diagram :
    Zigzag.MovingDiagram.wordAction Word.ForwardTriple.collapse
      (((ForwardZigzag.diagram W α hA hB).append
        (ForwardZigzag.diagram W β hB hE)).append (ForwardZigzag.diagram W γ hE hF)) =
      ForwardZigzag.diagram W (α ≫ β ≫ γ) hA hF := by
  apply Zigzag.MovingDiagram.ext
  · intro d
    exact collapse_append (α.app d) (β.app d) (γ.app d)
  · intro d e f i
    change Fin 2 at i
    cases i using Fin.cases with
    | zero =>
      exact (Zigzag.MovingHom.app_heq _ Word.ForwardTriple.cut_zero).trans
        ((((ForwardZigzag.diagram W α hA hB).append
          (ForwardZigzag.diagram W β hB hE)).append
            (ForwardZigzag.diagram W γ hE hF)).first f)
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (Zigzag.MovingHom.app_heq _ Word.ForwardTriple.cut_last).trans
        ((((ForwardZigzag.diagram W α hA hB).append
          (ForwardZigzag.diagram W β hB hE)).append
            (ForwardZigzag.diagram W γ hE hF)).last f)

end SerrePositivity.EInfinity.Hammock.ForwardTriple
