module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagEndpointChange
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.MarkedZigzagTransport

/-!
# 元の端点表示を含む関手の異種等式から厳密な回収

概要：端点の等式を移す元の関手を後合成すると、同じ元の関手へ厳密に戻る。
方針：端点表示で帰納し、元の関手の異種等式を使う。
規約：元の全対象・全列・全縦射を保持する。
使われ方：切断因子の同じ hammock 余極限の標準射の比較。
-/

@[expose] public section
universe u v uD vD
namespace SerrePositivity.EInfinity.Hammock.Zigzag.EndpointChange
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {X X' Y Y' : C}

lemma comp_eq_of_heq (hX : X = X') (hY : Y = Y')
    (F : D ⥤ Zigzag W w X Y) (G : D ⥤ Zigzag W w X' Y') (hFG : HEq F G) :
    F ⋙ functor hX hY = G := by
  cases hX
  cases hY
  simpa only [functor_refl, Functor.comp_id] using eq_of_heq hFG

end SerrePositivity.EInfinity.Hammock.Zigzag.EndpointChange
