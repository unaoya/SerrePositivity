module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PathSquareCurry
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.RelativePathFiniteComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathKanComparisonRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathKanPointComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathTransportTarget
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativePathValuePoint

/-!
概要：元の二入力を持つ有限 Kan 引き戻し射を、元の境界円柱を保って一値で検出する。
方針：有限相対 path 比較を実際の Kan 引き戻し内へ移し、三座標で制限を照合する。
規約：元の境界値・全輸送円柱・構成済み比較射を保持。
使われ方：一般 coherent filtered 引き戻し比較の相対有限持ち上げ。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：元の二入力と境界を持つ有限標的射は、全境界輸送を保って元の一値で検出できる。
方針：全相対境界付きの近似・輸送・反映を実際の比較へ合成する。
規約：境界制限は厳密な射の等式。使われ方：一般 coherent 引き戻しの相対比較。 -/
lemma fiberwisePullbackKanComparison_original_input_relative_detection
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f ≫ p)] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g)
    (H₀ : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H))
    (ha : ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) :
    ∃ b : B _⦋0⦌,
      ∃ t : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b),
      ∃ w : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b), A.ι ≫ w = t ∧
      ∃ L : SSet.Homotopy a (t ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b),
      ∃ G : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v H₀)
        (w ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueKanComparison p f g b),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g) ≫
            _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h =
      (u ≫ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H := H₀.h₀
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h =
      (v ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H := H₀.h₁
  obtain ⟨M, m, q, d, hk, he, r, hr, T, hT, ht⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_relativePathFiniteComparison p f g A u v a hu hv
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h) h₀ h₁ ha
  obtain ⟨G, hl, hr', hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePath_kan_point_comparison d hk he r hr H₀ T hT
  exact ⟨d.vertex, d.boundaryValue, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr, ht, d.boundaryHomotopy,
    G, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathKanComparison_restrict d hk he T.h hT G.h hl hr' hp⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
