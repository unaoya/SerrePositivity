module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundaryDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathFiniteApproximation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.RelativePathFiniteModelTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathModelComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTransportTarget
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathValuePoint

/-!
概要：指定 Kan path の有限近似から元の値への相対比較を実際に構成する。
方針：全境界付き有限近似、同時輸送、元の値への反映と全円柱の合成。
規約：追加の輸送や充填を仮定しない。使われ方：一般 coherent 引き戻しの相対有限検出。

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

/-- 概要：元の全相対境界輸送を保つ、一値へ反映した path との比較が存在する。
方針：単射有限近似・相対輸送・境界固定反映の実際の構成を合成。
規約：一般の filtered 底、元の三全空間。使われ方：相対 Kan 引き戻し比較の正方形。 -/
lemma exists_relativePathFiniteComparison {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f ≫ p)] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g)
    (r₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H)
    (hr₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ r₀ = (u ≫ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
    (hr₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ r₀ = (v ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
    (hra : ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ r₀ =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) :
    ∃ (M : SSet.{u}) (m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M) (q : M ⟶ H),
      ∃ d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q,
      ∃ (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
        (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g)),
      ∃ (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex)
        (hr : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d),
      ∃ T : SSet.Homotopy r₀ (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H),
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H ∧
        A.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr = d.boundaryValue := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a =
      A.ι ≫ (u ≫ f) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_zero, ← Category.assoc, ← hu, Category.assoc]
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a =
      A.ι ≫ (v ≫ g) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_one, ← Category.assoc, ← hv, Category.assoc]
  obtain ⟨M, m, q, z, hM, hm, hmq, hz, U, hU⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_relative_path_finite_approximation A (u ≫ f) (v ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a) h₀ h₁ r₀ hr₀ hr₁ hra
  let := hM
  let := hm
  have hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a := by
    rw [Category.assoc, hmq, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram_side]
  have he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g) := by
    rw [Category.assoc, hmq, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryDiagram_ends]
  obtain ⟨d, w, hw, G, hG, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_relativePathFiniteModelTransport p f g A u v a hu hv m q hk he
  have hU' : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      CartesianMonoidalCategory.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        m ≫ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H := by
    rw [hU, ← hmq, Category.assoc]
  obtain ⟨r, hr, T, hT, ha⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePath_model_comparison p f g A u v a m q d hk he
    w hw G hG z hz r₀ U hU'
  exact ⟨M, m, q, d, hk, he, r, hr, T, hT, ha⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
