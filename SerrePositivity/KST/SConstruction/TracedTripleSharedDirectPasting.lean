module
public import SerrePositivity.KST.SConstruction.TracedTripleOuterStagePasting
public import SerrePositivity.KST.SConstruction.FixedCylinderComparisonAttachment
public import SerrePositivity.KST.SConstruction.TracedBFTripleDirectCorrectionComparison

/-! # 元の十面複体の左右直接補正辺を同じ全比較円柱で結ぶ
概要：元の左右段面の直接補正辺を、保存済みの同じ全境界固定比較円柱で接続する。
方針：入口と全境界を固定して元の円柱を貼り、出口を既存右直接補正辺全体へ同定する。
規約：元の全十面・両円柱・全直接比較円柱と、その厳密な両全辺を保持する。
使われ方：元の raw BF 二三角形の接続と、共有直接補正の同じ辺路の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial

/-- 元の左右段面の下面を同じ全比較円柱で結ぶ実複体。 -/
def tripleSharedDirectPasting : SSet.{u} :=
  fixedCylinderComparisonAttachment (SSet.boundary.{u} 1).ι
    (stdSimplex.δ 2 ≫ outerStagePastingLeftCell) (stdSimplex.δ 2 ≫ outerStagePastingRightCell)

/-- 元の全十面・両正規化円柱の実複体全体の同じ像。 -/
def tripleSharedDirectPastingOriginal : outerStagePasting.{u} ⟶ tripleSharedDirectPasting :=
  fixedCylinderComparisonOriginal (SSet.boundary.{u} 1).ι
    (stdSimplex.δ 2 ≫ outerStagePastingLeftCell) (stdSimplex.δ 2 ≫ outerStagePastingRightCell)

/-- 元の共有直接補正の全比較円柱の同じ像。 -/
def tripleSharedDirectPastingCell : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ tripleSharedDirectPasting :=
  fixedCylinderComparisonCell (SSet.boundary.{u} 1).ι
    (stdSimplex.δ 2 ≫ outerStagePastingLeftCell) (stdSimplex.δ 2 ≫ outerStagePastingRightCell)

/-- 比較入口は、実複体内で元の左段面の同じ全直接補正辺。 -/
lemma tripleSharedDirectPasting_source :
    SSet.ι₀ ≫ tripleSharedDirectPastingCell.{u} =
      stdSimplex.δ 2 ≫ outerStagePastingLeftCell ≫ tripleSharedDirectPastingOriginal :=
  fixedCylinderComparison_source _ _ _

/-- 比較出口も、実複体内で元の右段面の同じ全直接補正辺。 -/
lemma tripleSharedDirectPasting_target :
    SSet.ι₁ ≫ tripleSharedDirectPastingCell.{u} =
      stdSimplex.δ 2 ≫ outerStagePastingRightCell ≫ tripleSharedDirectPastingOriginal :=
  fixedCylinderComparison_target _ _ _

/-- 元の第二 BF whisker に当たる、同じ実複体内の元の全交換上辺。 -/
def tripleSharedDirectSecondWhisker : (Δ[1] : SSet.{u}) ⟶ tripleSharedDirectPasting :=
  stdSimplex.δ 0 ≫ correctionInterchangePastingFirst ≫ correctionNormalizationPastingOriginal ≫
    outerBinaryPastingOriginal ≫ outerStagePastingOriginal ≫ tripleSharedDirectPastingOriginal

/-- 元の第一 BF whisker に当たる、同じ実複体内の元の後二射全段上辺。 -/
def tripleSharedDirectFirstWhisker : (Δ[1] : SSet.{u}) ⟶ tripleSharedDirectPasting :=
  stdSimplex.δ 0 ≫ triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫
    correctionInterchangePastingOriginal ≫ correctionNormalizationPastingOriginal ≫
      outerBinaryPastingOriginal ≫ outerStagePastingOriginal ≫ tripleSharedDirectPastingOriginal

variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の十面・両正規化円柱・共有直接補正の全比較円柱を同時に保持する実写像。 -/
def monicKTracedTripleSharedDirectPasting (n : ℕ) :
    tripleSharedDirectPasting.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  fixedCylinderComparisonMap (SSet.boundary 1).ι
    (stdSimplex.δ 2 ≫ outerStagePastingLeftCell) (stdSimplex.δ 2 ≫ outerStagePastingRightCell)
    (monicKTracedTripleOuterStagePasting F f g h n) (monicKTracedTripleDirectComparison F f g h n)
    (monicKTracedTripleOuterStagePasting_left_first F f g h n)
    (monicKTracedTripleOuterStagePasting_right_first F f g h n)
    (fixedBoundaryHomotopy_source _ _ _ (monicKTracedTripleDirectComparison_relative F f g h n))

/-- 元の全十面・両正規化円柱の実複体全体を厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectPasting_original (n : ℕ) :
    tripleSharedDirectPastingOriginal ≫ monicKTracedTripleSharedDirectPasting F f g h n =
      monicKTracedTripleOuterStagePasting F f g h n :=
  fixedCylinderComparisonMap_original _ _ _ _ _ _ _ _

/-- 元の共有直接補正の同じ全比較円柱そのものも厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectPasting_cell (n : ℕ) :
    tripleSharedDirectPastingCell ≫ monicKTracedTripleSharedDirectPasting F f g h n =
      (monicKTracedTripleDirectComparison F f g h n).h :=
  fixedCylinderComparisonMap_cell _ _ _ _ _ _ _ _

/-- 元の指定左 BF 比較辺の同じ全 raw 段評価を厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectPasting_left_comparison (n : ℕ) :
    stdSimplex.δ 0 ≫ outerStagePastingLeftCell ≫ tripleSharedDirectPastingOriginal ≫
        monicKTracedTripleSharedDirectPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedNativeTriplePrescribedEdge F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleSharedDirectPasting_original]
  exact monicKTracedTripleOuterStagePasting_left_comparison F f g h n

/-- 元の指定右 BF 比較辺の同じ全 raw 段評価も厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectPasting_right_comparison (n : ℕ) :
    stdSimplex.δ 0 ≫ outerStagePastingRightCell ≫ tripleSharedDirectPastingOriginal ≫
        monicKTracedTripleSharedDirectPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f (g ≫ h)).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleSharedDirectPasting_original]
  exact monicKTracedTripleOuterStagePasting_right_comparison F f g h n

/-- 元の第二 BF whisker の同じ全 raw 段辺も厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectPasting_second_whisker (n : ℕ) :
    tripleSharedDirectSecondWhisker ≫ monicKTracedTripleSharedDirectPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [tripleSharedDirectSecondWhisker]
  simp only [Category.assoc]
  rw [monicKTracedTripleSharedDirectPasting_original,
    monicKTracedTripleOuterStagePasting_original, monicKTracedTripleOuterBinaryPasting_original,
    monicKTracedTripleNormalizedPasting_original]
  exact monicKTracedTripleInterchangePasting_second_whisker F f g h n

/-- 元の第一 BF whisker の同じ全 raw 段辺も厳密に回収する。 -/
lemma monicKTracedTripleSharedDirectPasting_first_whisker (n : ℕ) :
    tripleSharedDirectFirstWhisker ≫ monicKTracedTripleSharedDirectPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [tripleSharedDirectFirstWhisker]
  simp only [Category.assoc]
  rw [monicKTracedTripleSharedDirectPasting_original,
    monicKTracedTripleOuterStagePasting_original, monicKTracedTripleOuterBinaryPasting_original,
    monicKTracedTripleNormalizedPasting_original]
  exact monicKTracedTripleInterchangePasting_first_whisker F f g h n

end SerrePositivity.KST.SConstruction
