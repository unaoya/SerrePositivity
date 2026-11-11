module
public import SerrePositivity.KST.SConstruction.TracedTripleRawComparisonStages
public import SerrePositivity.KST.SConstruction.RawComparisonAdjacentBoundary
public import SerrePositivity.KST.SConstruction.EndpointFixedCylinderEvaluation

/-! # 零段固定の第四辺比較の隣接段境界問題
概要：元の全段比較円柱を raw 評価の表示へ移し、隣接段の両全境界の一致を証明する。
方針：元の同じ全円柱を保存した表示移送と、raw 族の厳密な構造適合を使う。
規約：比較すべき全二次元写像と全境界を公開する。相対高次比較の存在は未証明。
使われ方：元の高次 prism からの構造適合比較と、全境界を固定する逐次厳密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 零段を固定する同じ全円柱族を、元の両 raw 辺の段評価の表示へ移す。 -/
def monicKTracedTripleRawComparisonLevelHomotopy (n : ℕ) : SSet.Homotopy
    (SSet.yonedaEquiv.symm ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z))).edge ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)
    (SSet.yonedaEquiv.symm ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z))).edge ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n) :=
  endpointFixedCylinderEvaluation
    ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z)))
    ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z)))
    (RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)
    (monicKTracedTripleRawComparisonStages F f g h n)

/-- raw 評価の表示へ移しても、元の同じ全円柱を厳密に保持する。 -/
lemma monicKTracedTripleRawComparisonLevelHomotopy_h (n : ℕ) :
    (monicKTracedTripleRawComparisonLevelHomotopy F f g h n).h =
      (monicKTracedTripleRawComparisonStages F f g h n).homotopy.h :=
  endpointFixedCylinderEvaluation_h _ _ _ _

/-- 表示を移しても元の入力区間の全境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleRawComparisonLevelHomotopy_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleRawComparisonLevelHomotopy F f g h n).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm ((monicKTracedNativeTriplePrescribedEdge F f g h).map
          (kRawMappingProjection (F.obj w) (F.obj z))).edge ≫
            RawSpectrumMapping.evaluation
              (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n :=
  endpointFixedCylinderEvaluation_relative _ _ _ _

/-- 零段の元の全高次比較は、この表示でも同じ全円柱を指定面に保持する。 -/
lemma monicKTracedTripleRawComparisonLevelHomotopy_zero_realization :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      (monicKTracedTripleRawComparisonLevelHomotopy F f g h 0).h :=
  (monicKTracedTripleRawComparisonStages_zero_realization F f g h).trans
    (monicKTracedTripleRawComparisonLevelHomotopy_h F f g h 0).symm

/-- 次段の元の全円柱の、同じ単射構造射による制限。 -/
def monicKTracedTripleRawAdjacentSource (n : ℕ) :=
  (monicKTracedTripleRawComparisonLevelHomotopy F f g h (n + 1)).h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj w)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space

/-- 前段の元の全円柱の、同じ raw 構造作用による像。 -/
def monicKTracedTripleRawAdjacentTarget (n : ℕ) :=
  (monicKTracedTripleRawComparisonLevelHomotopy F f g h n).h ≫
    RawSpectrumMapping.step (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n

/-- 隣接段で比較すべき両全写像は、入力境界と比較時刻の両端の和で厳密に一致する。 -/
lemma monicKTracedTripleRawAdjacent_boundary (n : ℕ) :
    fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
        monicKTracedTripleRawAdjacentSource F f g h n =
      fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫
        monicKTracedTripleRawAdjacentTarget F f g h n :=
  rawComparisonAdjacent_boundary (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z))
    (SSet.boundary 1).ι _ _ (monicKTracedTripleRawComparisonLevelHomotopy F f g h)
    (monicKTracedTripleRawComparisonLevelHomotopy_relative F f g h) n

end SerrePositivity.KST.SConstruction
