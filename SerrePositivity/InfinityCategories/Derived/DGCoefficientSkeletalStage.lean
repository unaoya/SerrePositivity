module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientSkeletalStep
public import SerrePositivity.InfinityCategories.Derived.FixedDiagramHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGClosedVerdierComposition

/-! # 有限相対骨格で保持する係数充填の状態

概要：最初の境界と商図式を固定し、分母・元係数・商全体と比較を各骨格段で保持する。
方針：元係数の厳密制限と比較正方形、境界を全時刻固定する比較を同じ状態に束ねる。
規約：閉分母は元の始点へ向かう。使われ方：一般有限対の係数充填の有限帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (a : L ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 元の部分係数と商全体から進める、相対骨格 n の実状態。 -/
structure DGCoefficientSkeletalStage where
  source : D
  denominator : ForgetEnrichment.of (Complex A) source ⟶ ForgetEnrichment.of (Complex A) x
  denominator_mem : (dgClosedEdge A D denominator).edge ∈ dgVerdierEdges A D P
  sourceMap : (skeletonOfMono i n : SSet) ⟶ DGNerve.pinchedHom A D source y
  quotientMap : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
    ((inclusion A D P).obj source) ((inclusion A D P).obj y)
  boundary : skeletonBase i n ≫ sourceMap = a ≫ pinchedClosedPrecomposition A D denominator
  square : sourceMap ≫ pinchedHomChainMap ((inclusion A D P).map source y) =
    (skeletonOfMono i n).ι ≫ quotientMap
  homotopy : SSet.Homotopy
    (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator)) quotientMap
  fixed : (i ▷ (Δ[1] : SSet.{max u v})) ≫ homotopy.h =
    fst L Δ[1] ≫ i ≫ g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator)

end SerrePositivity.InfinityCategories
