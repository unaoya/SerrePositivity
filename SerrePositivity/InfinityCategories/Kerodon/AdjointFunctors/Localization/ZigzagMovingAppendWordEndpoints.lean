module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendTransport

/-!
# 語と端点関手の表示を同時に移した連結

概要：語・共有端点の等式と元の図式の異種等式を連結へ渡す。
方針：表示の等式で帰納し、元の連結を回収する。
規約：元の全頂点・横列・縦射を保持する。
使われ方：切断した prefix・残りを元の恒等列付き図式へ照合する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a a' b b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {A A' B B' E E' : D ⥤ C}

lemma append_heq_word_endpoints (ha : a = a') (hb : b = b')
    (hA : A = A') (hB : B = B') (hE : E = E')
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B} {F' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a' A' B'}
    {G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B E} {G' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b' B' E'}
    (hF : HEq F F') (hG : HEq G G') : HEq (F.append G) (F'.append G') := by
  cases ha
  cases hb
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_heq_endpoints hA hB hE hF hG

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_heq_word_endpoints)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
