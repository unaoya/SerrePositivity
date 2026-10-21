module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramAppend

/-!
# 端点関手の表示変更と元の全図式の連結

概要：共有端点を含む図式の異種等式を連結した全図式へ移す。
方針：元の端点関手と図式の等式で帰納する。
規約：元の全縦射と接合点の縦射を保持する。
使われ方：prefix・残りの再添字の全図式の照合。
-/

@[expose] public section
universe u v uD vD
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : Word}
  {A A' B B' E E' : D ⥤ C}

lemma append_heq_endpoints (hA : A = A') (hB : B = B') (hE : E = E')
    {F : MovingDiagram D C W a A B} {F' : MovingDiagram D C W a A' B'}
    {G : MovingDiagram D C W b B E} {G' : MovingDiagram D C W b B' E'}
    (hF : HEq F F') (hG : HEq G G') : HEq (F.append G) (F'.append G') := by
  cases hA
  cases hB
  cases hE
  cases hF
  cases hG
  rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
