module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagram

/-!
# 動く端点を持つ図式の外延性

概要：全対象の等式と全縦射の成分の異種等式から図式自体を同定する。
方針：対象の族を先に同定し、全縦射の成分の外延性を使う。
規約：両端の元の関手は共通。局所端点の定数性は要求しない。
使われ方：抽出と再構成を元の局所図式に厳密に戻す。
-/

@[expose] public section
universe u v u' v'
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {A B : D ⥤ C}

lemma ext (F G : MovingDiagram D C W w A B) (ho : ∀ d, F.obj d = G.obj d)
    (hm : ∀ {d d'} (f : d ⟶ d') i, HEq ((F.map f).app i) ((G.map f).app i)) : F = G := by
  cases F with
  | mk Fo Fm Fi Fc Ff Fl =>
    cases G with
    | mk Go Gm Gi Gc Gf Gl =>
      dsimp only at ho hm
      have he : Fo = Go := funext ho
      cases he
      have he : @Fm = @Gm := by
        funext d d' f
        exact MovingHom.ext _ _ (fun i => eq_of_heq (hm f i))
      cases he
      rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
