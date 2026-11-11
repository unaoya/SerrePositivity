module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanRelativeReflection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathValuePoint

/-!
概要：輸送した有限 path 模型の Kan 像を、元の値へ全相対境界を固定して反映する。
方針：元の単位の強変形 retract による相対反映を使い、元の値の引き戻し射を読む。
規約：比較円柱は全相対境界上で定値、返す値の射は元の境界値と厳密に一致する。
使われ方：一般 coherent filtered 引き戻しの境界付き相対有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：輸送した指定 Kan path は全相対境界を固定して元の値へ反映できる。
方針：単位の自然性で全境界を照合し、相対反映と三座標の持ち上げを使う。
規約：元の境界値との制限式は等式。使われ方：相対有限検出の元の値の充填。 -/
lemma relativePath_model_reflection {K M E D H B : SSet.{u}}
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M) (q : M ⟶ H)
    (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)
    (w : M ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex) (hw : m ≫ w = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d)
    (z : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj M)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ z = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app M) :
    ∃ (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex)
      (hr : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d),
      ∃ G : SSet.Homotopy (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex))
        (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map w),
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
            _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d ≫
              _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex) ∧
        A.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr = d.boundaryValue := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p d.vertex
  have h : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map w) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex) := by
    rw [← Category.assoc, hz, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality,
      Functor.id_map, ← Category.assoc, hw]
  obtain ⟨r, hr, G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_relative_reflection
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d)
    (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map w) h
  exact ⟨r, hr, G, hG, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint_restrict d r hr⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
