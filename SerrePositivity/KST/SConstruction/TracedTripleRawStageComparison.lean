module
public import SerrePositivity.KST.SConstruction.TracedTripleRawDiagramPasting
public import SerrePositivity.KST.SConstruction.TripleRawDiagramKanValue

/-! # 元の指定第四辺と生成第四辺の全端点固定 raw 段比較
概要：元の全十二面・全円柱の関係から同じ辺の類を得て、実比較三角形と円柱を構成する。
方針：同じ実複体の raw 段写像に六対角面の消去を適用し、Kan 性で比較を実現する。
規約：各段の比較であり、隣接段との構造適合や全 raw 列への束ねは別工程。
使われ方：指定 BF 第四辺への全段比較を、零段固定で相対逐次厳密化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の同じ全十二面を用いた指定第四辺と生成第四辺の raw 段の類の一致。 -/
lemma monicKTracedTripleRawStageComparison_class (n : ℕ) :
    SSet.HomotopyCategory.homMk ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)) =
    SSet.HomotopyCategory.homMk ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)) := by
  apply tripleRawDiagramPasting_edge_class
    (monicKTracedTripleRawDiagramPasting F f g h n)
  · rw [monicKTracedTripleRawDiagramPasting_original,
      monicKTracedTripleSharedDirectRealizationPasting_original,
      monicKTracedTripleSharedDirectPasting_left_comparison]
    rw [SSet.Edge.map_edge, SSet.yonedaEquiv_symm_comp]
  · rw [monicKTracedTripleRawDiagramPasting_generated]
    rw [SSet.Edge.map_edge, SSet.yonedaEquiv_symm_comp]

/-- 元の同じ二辺と恒等終辺を全三面に持つ実比較三角形。 -/
def monicKTracedTripleRawStageComparisonTriangle (n : ℕ) :
    SSet.Edge.CompStruct ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n))
      (SSet.Edge.id _) ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)) := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply Nonempty.some
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  change SSet.HomotopyCategory.homMk _ ≫
    SSet.HomotopyCategory.homMk (SSet.Edge.id _) = _
  rw [SSet.HomotopyCategory.homMk_id, Category.comp_id]
  exact monicKTracedTripleRawStageComparison_class F f g h n

/-- 元の指定左辺と生成第四辺の raw 段評価を結ぶ全端点固定実円柱。 -/
def monicKTracedTripleRawStageComparison (n : ℕ) :
    EndpointFixedEdgeCylinder ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n))
      ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)) :=
  ⟨endpointFixedTriangleHomotopy (monicKTracedTripleRawStageComparisonTriangle F f g h n),
    endpointFixedTriangleHomotopy_relative
      (monicKTracedTripleRawStageComparisonTriangle F f g h n)⟩

/-- 全比較円柱は元の入力区間境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleRawStageComparison_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleRawStageComparison F f g h n).homotopy.h =
      CartesianMonoidalCategory.fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation
          (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n))).edge :=
  (monicKTracedTripleRawStageComparison F f g h n).relative

/-- 円柱は、その構成に用いた同じ全比較三角形を指定面に厳密に保持する。 -/
lemma monicKTracedTripleRawStageComparison_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ (monicKTracedTripleRawStageComparison F f g h n).homotopy.h =
      SSet.yonedaEquiv.symm
        (monicKTracedTripleRawStageComparisonTriangle F f g h n).simplex :=
  endpointFixedTriangleHomotopy_triangle _

end SerrePositivity.KST.SConstruction
