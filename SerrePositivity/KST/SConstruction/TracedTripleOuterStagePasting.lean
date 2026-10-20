module
public import SerrePositivity.KST.SConstruction.TracedTripleOuterBinaryPasting
public import SerrePositivity.KST.SConstruction.OuterStagePasting
public import SerrePositivity.KST.SConstruction.TracedBFTripleRawBoundary

/-! # 元の全十面・両円柱を保持する三入力の外側段面接続
概要：元の八面・両円柱へ元の左右外側段三角形全体を同じ全対角辺で接続する。
方針：二部分三角形の元の全対角補正辺と、元の段三角形の同じ全辺を照合する。
規約：全十面・両円柱・元の直接補正辺と BF 比較辺を厳密に保持する。
使われ方：元の共有直接補正と raw BF 二三角形を同じ比較複体へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の十全段面・二部分面・交換面と両全円柱を同時に保持する実写像。 -/
def monicKTracedTripleOuterStagePasting (n : ℕ) :
    outerStagePasting.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  outerStagePastingMap (monicKTracedTripleOuterBinaryPasting F f g h n)
    (SSet.yonedaEquiv.symm
      (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle.simplex)
    (SSet.yonedaEquiv.symm
      (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle.simplex)
    ((monicKTracedTripleOuterBinaryPasting_left_direct F f g h n).trans
      (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle).symm)
    ((monicKTracedTripleOuterBinaryPasting_right_direct F f g h n).trans
      (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
        (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle).symm)

/-- 元の全八面・両全正規化円柱を持つ比較複体全体を厳密に回収する。 -/
lemma monicKTracedTripleOuterStagePasting_original (n : ℕ) :
    outerStagePastingOriginal ≫ monicKTracedTripleOuterStagePasting F f g h n =
      monicKTracedTripleOuterBinaryPasting F f g h n :=
  outerStagePastingMap_original _ _ _ _ _

/-- 元の左外側全段三角形そのものを厳密に回収する。 -/
lemma monicKTracedTripleOuterStagePasting_left (n : ℕ) :
    outerStagePastingLeftCell ≫ monicKTracedTripleOuterStagePasting F f g h n =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle.simplex :=
  outerStagePastingMap_left _ _ _ _ _

/-- 元の右外側全段三角形そのものも厳密に回収する。 -/
lemma monicKTracedTripleOuterStagePasting_right (n : ℕ) :
    outerStagePastingRightCell ≫ monicKTracedTripleOuterStagePasting F f g h n =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle.simplex :=
  outerStagePastingMap_right _ _ _ _ _

/-- 左外側の元の直接補正辺を同じ全下面として回収する。 -/
lemma monicKTracedTripleOuterStagePasting_left_first (n : ℕ) :
    stdSimplex.δ 2 ≫ outerStagePastingLeftCell ≫
        monicKTracedTripleOuterStagePasting F f g h n =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).first.edge := by
  rw [monicKTracedTripleOuterStagePasting_left]
  exact SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm _

/-- 右外側の元の直接補正辺も同じ全下面として回収する。 -/
lemma monicKTracedTripleOuterStagePasting_right_first (n : ℕ) :
    stdSimplex.δ 2 ≫ outerStagePastingRightCell ≫
        monicKTracedTripleOuterStagePasting F f g h n =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).first.edge := by
  rw [monicKTracedTripleOuterStagePasting_right]
  exact SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm _

/-- 左外側の全上辺は、元の指定左 BF 比較辺の同じ全 raw 段評価。 -/
lemma monicKTracedTripleOuterStagePasting_left_comparison (n : ℕ) :
    stdSimplex.δ 0 ≫ outerStagePastingLeftCell ≫
        monicKTracedTripleOuterStagePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedNativeTriplePrescribedEdge F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleOuterStagePasting_left, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm,
    monicKTracedCompositionRawStageEdge_map, monicKTracedNativeTriplePrescribedEdge_edge]

/-- 右外側の全上辺も、元の指定右 BF 比較辺の同じ全 raw 段評価。 -/
lemma monicKTracedTripleOuterStagePasting_right_comparison (n : ℕ) :
    stdSimplex.δ 0 ≫ outerStagePastingRightCell ≫
        monicKTracedTripleOuterStagePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f (g ≫ h)).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleOuterStagePasting_right, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm,
    monicKTracedCompositionRawStageEdge_map]

end SerrePositivity.KST.SConstruction
