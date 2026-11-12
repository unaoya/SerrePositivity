module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagram

/-!
# 動く端点を持つ図式の外延性

概要：全対象の等式と全縦射の成分の異種等式から図式自体を同定する。
方針：対象の族を先に同定し、全縦射の成分の外延性を使う。
規約：両端の元の関手は共通。局所端点の定数性は要求しない。
使われ方：抽出と再構成を元の局所図式に厳密に戻す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}

lemma ext (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B) (ho : ∀ d, F.obj d = G.obj d)
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
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext _ _ (fun i => eq_of_heq (hm f i))
      cases he
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (ext)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
