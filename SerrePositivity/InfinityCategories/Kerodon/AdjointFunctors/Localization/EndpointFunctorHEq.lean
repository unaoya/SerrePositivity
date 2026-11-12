module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagTransport

/-!
# 元の端点表示を含む関手の異種等式から厳密な回収

概要：端点の等式を移す元の関手を後合成すると、同じ元の関手へ厳密に戻る。
方針：端点表示で帰納し、元の関手の異種等式を使う。
規約：元の全対象・全列・全縦射を保持する。
使われ方：切断因子の同じ hammock 余極限の標準射の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y Y' : C}

lemma comp_eq_of_heq (hX : X = X') (hY : Y = Y')
    (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (G : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y') (hFG : HEq F G) :
    F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor hX hY = G := by
  cases hX
  cases hY
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor_refl, Functor.comp_id] using eq_of_heq hFG

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.EndpointChange.comp_eq_of_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (comp_eq_of_heq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
