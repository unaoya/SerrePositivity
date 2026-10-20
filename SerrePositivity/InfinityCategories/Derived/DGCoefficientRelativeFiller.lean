module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientSkeletalStage

/-! # 閉分母後の一般相対係数充填

概要：任意の単体集合対の係数充填と、指定部分上で全時刻定値な商比較を表す。
方針：閉分母、元係数全体、厳密な部分制限と比較を一つの実データへ束ねる。
規約：比較は元の商図式から充填の商像へ向かう。使われ方：実屋根の有限相対充填。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (x y : D)
variable (a : L ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 合成閉分母後の実相対充填と、その境界を固定する商比較。 -/
structure DGCoefficientRelativeFiller where
  source : D
  denominator : ForgetEnrichment.of (Complex A) source ⟶ ForgetEnrichment.of (Complex A) x
  denominator_mem : (dgClosedEdge A D denominator).edge ∈ dgVerdierEdges A D P
  filler : K ⟶ DGNerve.pinchedHom A D source y
  boundary : i ≫ filler = a ≫ pinchedClosedPrecomposition A D denominator
  comparison : SSet.Homotopy
    (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator))
    (filler ≫ pinchedHomChainMap ((inclusion A D P).map source y))
  fixed : (i ▷ (Δ[1] : SSet.{max u v})) ≫ comparison.h =
    fst L Δ[1] ≫ i ≫ g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator)

end SerrePositivity.InfinityCategories
