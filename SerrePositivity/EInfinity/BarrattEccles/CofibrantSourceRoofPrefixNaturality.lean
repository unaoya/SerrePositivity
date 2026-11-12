module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrefixNaturality
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofPrefixHomotopy

/-!
# 実 cofibrant comma 上の元の全 prefix 円柱の自然性

概要：元の comma の始点射に対し全円柱が同じ前合成と厳密に一致する。
方針：元の U・p・σ を全円柱の自然性へ直接代入する。
規約：任意可換環・全 Under パラメータ・元の h を保持する。
使われ方：native roof 全三角形の coherent 合成条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaPrefixHomotopy_underMap
    {s t : cofibrantSourceRoofProductComma A X Y b} (a : s ⟶ t) :
    (nerveMap (Under.map a) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (cofibrantSourceRoofProductCommaPrefixHomotopy A X Y b s).h =
    (cofibrantSourceRoofProductCommaPrefixHomotopy A X Y b t).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (cofibrantAlgebraRelativeCategory A).weakEquivalences
        ((cofibrantSourceRoofProductCommaDiagram A X Y b).map a))
        (show (cofibrantAlgebraRelativeCategory A).category from Y) :=
  Hammock.LeftRoof.Prefix.arrowHomotopy_underMap
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) s a

end SerrePositivity.EInfinity.BarrattEccles
