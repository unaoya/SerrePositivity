module

public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackLifting
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.F1.Filtered.FiberwisePullbackKanRelativeLifting
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1.Filtered.FilteredLeftFibrationDetection
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.KanBoundaryHomotopyExtension
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.RelativeHomotopyCompositionAlongMap

/-!
概要：Kan 始域の任意の有限境界を持つ標的射へ、全境界円柱を保つ相対持ち上げを構成する。
方針：境界を元の値で検出し、標的境界をその全円柱で延長して元の境界の場合へ帰着する。
規約：境界が元の全空間の単位を経由することを仮定しない。
使われ方：実際の Kan 引き戻し比較の弱同値性の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：任意の Kan 境界を持つ有限標的射は、境界円柱を保って実際の比較へ持ち上がる。
方針：境界の元の値での検出・標的境界補正・二比較の同時合成。
規約：元の比較と全境界を保持。使われ方：境界での単位因子分解を要しない相対検査。 -/
lemma fiberwisePullbackKanComparison_finite_kan_boundary_lifting
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (a : (A : SSet.{u}) ⟶ continuousKanReplacement.obj (fiberwiseIntervalPullback p f g))
    (e : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (he : A.ι ≫ e = a ≫ fiberwisePullbackKanComparison p f g) :
    ∃ r : K ⟶ continuousKanReplacement.obj (fiberwiseIntervalPullback p f g),
      ∃ L : SSet.Homotopy a (A.ι ≫ r),
      ∃ G : SSet.Homotopy e (r ≫ fiberwisePullbackKanComparison p f g),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫ fiberwisePullbackKanComparison p f g := by
  obtain ⟨b, s, ⟨U⟩⟩ := continuousKanLeftFibration_finite_fiber_detection_unreplaced
    (fiberwiseIntervalPullbackProjection p f g) a
  let a₀ := s ≫ vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b
  let T : SSet.Homotopy (A.ι ≫ e)
      (a₀ ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
        fiberwisePullbackKanComparison p f g) :=
    { h := U.h ≫ fiberwisePullbackKanComparison p f g
      h₀ := by
        change SSet.ι₀ ≫ U.h ≫ fiberwisePullbackKanComparison p f g = A.ι ≫ e
        rw [← Category.assoc, U.h₀, ← he]
      h₁ := by
        change SSet.ι₁ ≫ U.h ≫ fiberwisePullbackKanComparison p f g =
          a₀ ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
            fiberwisePullbackKanComparison p f g
        rw [← Category.assoc, U.h₁]
        rfl
      rel := (functorHomotopyPostcomp U (fiberwisePullbackKanComparison p f g)).rel }
  obtain ⟨e₁, he₁, G₀, hG₀⟩ := kanComplex_extend_boundary_homotopy A.ι e _ T
  obtain ⟨r, V, G₁, hG₁⟩ :=
    fiberwisePullbackKanComparison_finite_relative_lifting p f g A a₀ e₁ he₁
  obtain ⟨L, G, hG⟩ := exists_relativeHomotopyCompositionAlongMap
    (X := continuousKanReplacement.obj (fiberwiseIntervalPullback p f g))
    A (fiberwisePullbackKanComparison p f g) U V G₀ G₁ hG₀ hG₁
  exact ⟨r, L, G, hG⟩

end SerrePositivity.InfinityCategories.F2
