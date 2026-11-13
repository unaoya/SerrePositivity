module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiberwisePullbackOriginalInputRelativeDetection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanRelativeBoundaryPath

/-!
概要：実際の境界可換式を持つ有限 Kan 引き戻し射を、元の境界円柱を保って一値で検出する。
方針：境界可換式から全 path を回収し、相対有限検出を適用する。
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
lemma fiberwisePullbackKanComparison_original_input_relative_detection_of_boundary
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f ≫ p)] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g)
    (H₀ : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H))
    (hb : A.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v H₀ = a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g) :
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
  have ha := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_relative_boundary_path p f g A.ι u v a H₀ hb
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.fiberwisePullbackKanComparison_original_input_relative_detection p f g A u v a hu hv H₀ ha

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
