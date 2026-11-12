module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanSpecifiedHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeHomotopyZigzag
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathModelReflection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTargetFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathTransportTarget
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathValuePoint

/-!
概要：有限 path 模型の近似・輸送・反映を全相対境界円柱を保って合成する。
方針：輸送を指定円柱のまま Kan 置換へ移し、相対反映を含めた zigzag を合成する。
規約：元の全境界輸送との一致を厳密な等式で返す。
使われ方：標的 Kan 引き戻し内の境界付き比較の正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の全相対境界輸送を保つ、元の値へ反映した path との比較。
方針：指定輸送の延長・相対反映・境界固定 zigzag の合成。
規約：反映後の射も元の境界値に一致。使われ方：相対有限検出の実際の比較。 -/
lemma relativePath_model_comparison {K M E D H B : SSet.{u}}
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (m : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A ⟶ M) (q : M ⟶ H)
    (d : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativePathInputTransportData p f g A u v a m q)
    (hk : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundarySide A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryEnds A ≫ m) ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (u ≫ f) (v ≫ g))
    (w : M ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex) (hw : m ≫ w = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d)
    (G : SSet.Homotopy q (w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex))
    (hG : (m ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h)
    (z : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj M)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ z = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app M)
    (r₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H)
    (U : SSet.Homotopy r₀ (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map q))
    (hU : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        m ≫ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) :
    ∃ (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p d.vertex)
      (hr : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathTransportTargetFiber d),
      ∃ T : SSet.Homotopy r₀ (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H),
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryTransportHomotopy d hk he).h ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H ∧
        A.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathValuePoint d r hr = d.boundaryValue := by
  obtain ⟨V, hV⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_specified_homotopy_precomp G
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A) m z hz
  obtain ⟨r, hr, R, hR, ha⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePath_model_reflection p f g A u v a m q d w hw z hz
  let W : SSet.Homotopy
      (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
      (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex)) :=
    { h := R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex)
      h₀ := by
        change SSet.ι₀ ≫ R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex) =
          r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H
        rw [← Category.assoc, R.h₀, Category.assoc,
          ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map]
      h₁ := by
        change SSet.ι₁ ≫ R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex) =
          z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex)
        rw [← Category.assoc, R.h₁, Category.assoc, ← Functor.map_comp]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  have hW : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ W.h =
      fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H := by
    change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫
      R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p d.vertex) = _
    rw [← Category.assoc, hR, Category.assoc, Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map, ← hr]
    simp only [Category.assoc]
  have hU' : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ≫ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map q := by
    rw [hU, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A), hz, Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map]
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyZigzag (Subcomplex.unionProd (boundary 1) A)
    U V W hU' hW
  change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ V.h at hT
  refine ⟨r, hr, T, ?_, ha⟩
  rw [hT, hV, ← Category.assoc, hG]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
