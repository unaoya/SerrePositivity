module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryBackwardLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagEndpointChange

/-!
# 元の境界の等式射による後合成と端点表示の移送

概要：先頭 backward の語への等式射の後合成は、元の端点の等式移送そのものである。
方針：端点の等式で帰納して元の恒等則へ戻す。
規約：元の全頂点・全列・全縦射の関手の厳密な一致を使う。
使われ方：固定対象の元の左係数図式の回収。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
open CategoryTheory
lemma backwardFunctor_eqToHom {B : Type u} [Category.{u} B]
    {W : MorphismProperty B} [W.IsMultiplicative] {w : Word} {X X' Y : B}
    (hX : X = X') (hf : W (eqToHom hX)) :
    backwardFunctor (W := W) (w := w) (Y := Y) (eqToHom hX) hf =
      Zigzag.EndpointChange.functor hX rfl := by
  cases hX
  exact backwardFunctor_id
end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
