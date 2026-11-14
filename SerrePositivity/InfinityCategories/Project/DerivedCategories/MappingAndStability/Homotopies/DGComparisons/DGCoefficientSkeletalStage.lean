module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGCoefficientSkeletalStep
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.FixedDiagramHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGClosedVerdierComposition

/-! # 有限相対骨格で保持する係数充填の状態

概要：最初の境界と商図式を固定し、分母・元係数・商全体と比較を各骨格段で保持する。
方針：元係数の厳密制限と比較正方形、境界を全時刻固定する比較を同じ状態に束ねる。
規約：閉分母は元の始点へ向かう。使われ方：一般有限対の係数充填の有限帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (a : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))

/-- 元の部分係数と商全体から進める、相対骨格 n の実状態。 -/
structure DGCoefficientSkeletalStage where
  source : D
  denominator : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) source ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x
  denominator_mem : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D denominator).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  sourceMap : (skeletonOfMono i n : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D source y
  quotientMap : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
    ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj source) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
  boundary : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i n ≫ sourceMap = a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D denominator
  square : sourceMap ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map source y) =
    (skeletonOfMono i n).ι ≫ quotientMap
  homotopy : SSet.Homotopy
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map denominator)) quotientMap
  fixed : (i ▷ (Δ[1] : SSet.{max u v})) ≫ homotopy.h =
    fst L Δ[1] ≫ i ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map denominator)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
