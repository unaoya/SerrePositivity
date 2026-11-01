module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendTransport

/-!
# 語と端点関手の表示を同時に移した連結

概要：語・共有端点の等式と元の図式の異種等式を連結へ渡す。
方針：表示の等式で帰納し、元の連結を回収する。
規約：元の全頂点・横列・縦射を保持する。
使われ方：切断した prefix・残りを元の恒等列付き図式へ照合する。
-/

@[expose] public section
universe u v uD vD
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a a' b b' : Word}
  {A A' B B' E E' : D ⥤ C}

lemma append_heq_word_endpoints (ha : a = a') (hb : b = b')
    (hA : A = A') (hB : B = B') (hE : E = E')
    {F : MovingDiagram D C W a A B} {F' : MovingDiagram D C W a' A' B'}
    {G : MovingDiagram D C W b B E} {G' : MovingDiagram D C W b' B' E'}
    (hF : HEq F F') (hG : HEq G G') : HEq (F.append G) (F'.append G') := by
  cases ha
  cases hb
  exact append_heq_endpoints hA hB hE hF hG

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
