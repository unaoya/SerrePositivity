module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryForwardLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange

/-!
# 元の境界の等式射による前合成と端点表示の移送

概要：先頭 forward の語への等式射の前合成は、元の端点の等式移送そのものである。
方針：端点の等式で帰納して元の恒等則へ戻す。
規約：元の全頂点・全列・全縦射の関手の厳密な一致を使う。
使われ方：固定対象の元の左係数図式の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
lemma forwardFunctor_eqToHom {B : Type u} [Category.{u} B]
    {W : MorphismProperty B} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : B} (hX : X = X') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor (W := W) (w := w) (Y := Y) (eqToHom hX.symm) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor hX rfl := by
  cases hX
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardFunctor_id

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardFunctor_eqToHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardFunctor_eqToHom)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
