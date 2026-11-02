module

public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackLifting
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanUnit
public import SerrePositivity.InfinityCategories.F2.Filtered.FiberwisePullbackRelativeOriginalBoundary
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPoint
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPointRecognition
public import SerrePositivity.InfinityCategories.F2.Filtered.KanCospanRelativeInputReduction
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.RelativeHomotopyCompositionAlongMap

/-!
概要：任意の有限 Kan 引き戻し射を、元の全境界円柱を保って元の一値で検出する。
方針：二入力の相対還元と元の二入力の場合の検出を、元の境界三角形の像で合成する。
規約：元の比較射そのものと、境界の射・全円柱を保持する。
使われ方：一般 coherent filtered 引き戻し比較の相対有限持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：任意の有限標的射は元の境界輸送を厳密に保って元の一値の実際の比較像へ移る。
方針：二入力還元・相対有限検出・元の境界三角形に沿う合成。
規約：元の入力を持つことを仮定しない。使われ方：一般の相対比較の有限検出。 -/
lemma fiberwisePullbackKanComparison_finite_relative_value_detection
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (e : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (he : A.ι ≫ e = a ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      fiberwisePullbackKanComparison p f g) :
    ∃ b : B _⦋0⦌,
      ∃ t : (A : SSet.{u}) ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b),
      ∃ w : K ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b), A.ι ≫ w = t ∧
      ∃ L : SSet.Homotopy a (t ≫ fiberwisePullbackValueToTotal p f g b),
      ∃ G : SSet.Homotopy e (w ≫ fiberwisePullbackValueKanComparison p f g b),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
          continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
            fiberwisePullbackKanComparison p f g := by
  let k := continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
    fiberwisePullbackKanComparison p f g
  have hkl : k ≫ intervalPullbackLeft (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) =
      fiberwiseIntervalPullbackLeft p f g ≫ continuousKanReplacementUnit.app E := by
    simpa only [k, intervalPullbackLeft, Category.assoc] using
      fiberwisePullbackKanComparison_unit_left p f g
  have hkr : k ≫ intervalPullbackRight (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) =
      fiberwiseIntervalPullbackRight p f g ≫ continuousKanReplacementUnit.app D := by
    simpa only [k, intervalPullbackRight, Category.assoc] using
      fiberwisePullbackKanComparison_unit_right p f g
  have hpl := fiberwiseIntervalPullback_left_projection p f g
  have hpr := fiberwiseIntervalPullback_right_projection p f g
  obtain ⟨a', u, v, hu, hv, T, e', he', hl, hr, U, hU⟩ := kanCospan_relative_input_reduction
    (fiberwiseIntervalPullbackProjection p f g) (f ≫ p) (g ≫ p)
    (fiberwiseIntervalPullbackLeft p f g) (fiberwiseIntervalPullbackRight p f g)
    hpl hpr f g k hkl hkr A a e he
  obtain ⟨P, hP⟩ := kanCospanPoint_recognition f g e' u v hl hr
  have hP' : A.ι ≫ kanCospanPoint f g u v P = a' ≫ k := by rw [← hP]; exact he'
  obtain ⟨b, t, w, hw, L, V, hV⟩ :=
    fiberwisePullbackKanComparison_original_input_relative_detection_of_boundary
      p f g A u v a' hu hv P hP'
  let U' : SSet.Homotopy e (kanCospanPoint f g u v P) :=
    { h := U.h
      h₀ := U.h₀
      h₁ := by
        change SSet.ι₁ ≫ U.h = kanCospanPoint f g u v P
        rw [U.h₁, hP]
      rel := U.rel }
  have : Quasicategory (fiberwiseIntervalPullback p f g) :=
    quasicategory_of_innerFibration (fiberwiseIntervalPullbackProjection p f g)
  obtain ⟨J, G, hG⟩ := exists_relativeHomotopyCompositionAlongMap
    (X := fiberwiseIntervalPullback p f g) A k T L U' V hU hV
  exact ⟨b, t, w, hw, J, G, hG⟩

end SerrePositivity.InfinityCategories.F2
