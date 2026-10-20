module
public import SerrePositivity.KST.SConstruction.TripleRawDiagramPasting

/-! # 元の BF 二面の全 raw 段評価を同じ実複体へ保持する
概要：元の BF 二三角形を射影・段評価し、既存の全比較族と同時に保持する。
方針：指定ホーンの全辺を既存の同じ BF 辺へ照合し、全三角形の接続へ渡す。
規約：二面は元の native diamond の全像そのものとし、選び直さない。
使われ方：指定第四辺と生成第四辺の端点固定 raw 比較の構成。
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

/-- 元の第一 BF 全面の同じ raw 段評価。 -/
def monicKTracedTripleRawFirstTriangle (n : ℕ) : (Δ[2] : SSet.{u}) ⟶
    (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
      ((kKanSequence (F.obj z)).level n).space).right :=
  SSet.yonedaEquiv.symm (monicKTracedNativeTripleCompositionDiamond F f g h).first.simplex ≫
    kRawMappingProjection (F.obj w) (F.obj z) ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n

/-- 元の第二 BF 全面の同じ raw 段評価。 -/
def monicKTracedTripleRawSecondTriangle (n : ℕ) : (Δ[2] : SSet.{u}) ⟶
    (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
      ((kKanSequence (F.obj z)).level n).space).right :=
  SSet.yonedaEquiv.symm (monicKTracedNativeTripleCompositionDiamond F f g h).second.simplex ≫
    kRawMappingProjection (F.obj w) (F.obj z) ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n

/-- 第一面の下面は既存の同じ右 BF 比較辺全体。 -/
lemma monicKTracedTripleRawFirstTriangle_lower (n : ℕ) :
    tripleRawFirstLower ≫ monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      stdSimplex.δ 2 ≫ monicKTracedTripleRawFirstTriangle F f g h n := by
  rw [tripleRawFirstLower]
  simp only [Category.assoc]
  rw [monicKTracedTripleSharedDirectRealizationPasting_original,
    monicKTracedTripleSharedDirectPasting_right_comparison]
  unfold monicKTracedTripleRawFirstTriangle
  simp only [← Category.assoc, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]

/-- 第一面の上辺も既存の同じ第一 whisker 全体。 -/
lemma monicKTracedTripleRawFirstTriangle_upper (n : ℕ) :
    tripleRawFirstUpper ≫ monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      stdSimplex.δ 0 ≫ monicKTracedTripleRawFirstTriangle F f g h n := by
  rw [tripleRawFirstUpper, Category.assoc,
    monicKTracedTripleSharedDirectRealizationPasting_original,
    monicKTracedTripleSharedDirectPasting_first_whisker]
  unfold monicKTracedTripleRawFirstTriangle
  simp only [← Category.assoc, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  all_goals rfl

/-- 第二面の上辺も既存の同じ第二 whisker 全体。 -/
lemma monicKTracedTripleRawSecondTriangle_upper (n : ℕ) :
    tripleRawSecondUpper ≫ monicKTracedTripleSharedDirectRealizationPasting F f g h n =
      stdSimplex.δ 0 ≫ monicKTracedTripleRawSecondTriangle F f g h n := by
  rw [tripleRawSecondUpper, Category.assoc,
    monicKTracedTripleSharedDirectRealizationPasting_original,
    monicKTracedTripleSharedDirectPasting_second_whisker]
  unfold monicKTracedTripleRawSecondTriangle
  simp only [← Category.assoc, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  all_goals rfl

/-- 元の BF 二面の raw 段評価は同じ全対角辺を共有する。 -/
lemma monicKTracedTripleRawTriangles_diagonal (n : ℕ) :
    stdSimplex.δ 1 ≫ monicKTracedTripleRawFirstTriangle F f g h n =
      stdSimplex.δ 1 ≫ monicKTracedTripleRawSecondTriangle F f g h n := by
  unfold monicKTracedTripleRawFirstTriangle monicKTracedTripleRawSecondTriangle
  simp only [← Category.assoc, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]

/-- 元の第一全 BF 面を既存の全比較族と同時に保持する実写像。 -/
def monicKTracedTripleRawFirstPasting (n : ℕ) : tripleRawFirstDomain.{u} ⟶
    (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
      ((kKanSequence (F.obj z)).level n).space).right :=
  specifiedTriangleAttachmentMap tripleRawFirstHorn
    (monicKTracedTripleSharedDirectRealizationPasting F f g h n)
    (monicKTracedTripleRawFirstTriangle F f g h n)
    (specifiedInnerHorn_map _ _ _
      (by rw [tripleRawFirstHorn_lower]; exact monicKTracedTripleRawFirstTriangle_lower F f g h n)
      (by rw [tripleRawFirstHorn_upper]; exact monicKTracedTripleRawFirstTriangle_upper F f g h n))

/-- 第一面の接続後も元の全十面・全比較族を厳密に回収する。 -/
lemma monicKTracedTripleRawFirstPasting_original (n : ℕ) :
    tripleRawFirstOriginal ≫ monicKTracedTripleRawFirstPasting F f g h n =
      monicKTracedTripleSharedDirectRealizationPasting F f g h n :=
  specifiedTriangleAttachmentMap_original _ _ _ _

/-- 元の第一 BF 全三角形そのものを厳密に回収する。 -/
lemma monicKTracedTripleRawFirstPasting_cell (n : ℕ) :
    tripleRawFirstCell ≫ monicKTracedTripleRawFirstPasting F f g h n =
      monicKTracedTripleRawFirstTriangle F f g h n :=
  specifiedTriangleAttachmentMap_cell _ _ _ _

/-- 元の両 BF 全面を全十面・全円柱・全高次比較と同時に保持する実写像。 -/
def monicKTracedTripleRawDiagramPasting (n : ℕ) : tripleRawDiagramPasting.{u} ⟶
    (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
      ((kKanSequence (F.obj z)).level n).space).right :=
  specifiedTriangleAttachmentMap tripleRawSecondHorn
    (monicKTracedTripleRawFirstPasting F f g h n)
    (monicKTracedTripleRawSecondTriangle F f g h n)
    (specifiedOuterHorn_map _ _ _
      (by
        rw [tripleRawSecondHorn_diagonal, Category.assoc,
          monicKTracedTripleRawFirstPasting_cell]
        exact monicKTracedTripleRawTriangles_diagonal F f g h n)
      (by
        rw [tripleRawSecondHorn_upper, tripleRawSecondAttachingUpper, Category.assoc,
          monicKTracedTripleRawFirstPasting_original]
        exact monicKTracedTripleRawSecondTriangle_upper F f g h n))

/-- 最終写像は元の第一 BF 面までの全複体を保持する。 -/
lemma monicKTracedTripleRawDiagramPasting_first_original (n : ℕ) :
    tripleRawDiagramPastingFirstOriginal ≫ monicKTracedTripleRawDiagramPasting F f g h n =
      monicKTracedTripleRawFirstPasting F f g h n :=
  specifiedTriangleAttachmentMap_original _ _ _ _

/-- 元の全十面・全円柱・全高次比較を同時に厳密に回収する。 -/
lemma monicKTracedTripleRawDiagramPasting_original (n : ℕ) :
    tripleRawDiagramPastingOriginal ≫ monicKTracedTripleRawDiagramPasting F f g h n =
      monicKTracedTripleSharedDirectRealizationPasting F f g h n := by
  rw [tripleRawDiagramPastingOriginal, Category.assoc,
    monicKTracedTripleRawDiagramPasting_first_original, monicKTracedTripleRawFirstPasting_original]

/-- 元の第一 BF 全三角形そのものも同じ実複体内で保持する。 -/
lemma monicKTracedTripleRawDiagramPasting_first (n : ℕ) :
    tripleRawDiagramPastingFirst ≫ monicKTracedTripleRawDiagramPasting F f g h n =
      monicKTracedTripleRawFirstTriangle F f g h n := by
  rw [tripleRawDiagramPastingFirst, Category.assoc,
    monicKTracedTripleRawDiagramPasting_first_original, monicKTracedTripleRawFirstPasting_cell]

/-- 元の第二 BF 全三角形そのものも同じ実複体内で保持する。 -/
lemma monicKTracedTripleRawDiagramPasting_second (n : ℕ) :
    tripleRawDiagramPastingSecond ≫ monicKTracedTripleRawDiagramPasting F f g h n =
      monicKTracedTripleRawSecondTriangle F f g h n :=
  specifiedTriangleAttachmentMap_cell _ _ _ _

/-- 新しい下面は元の生成第四 BF 辺の全 raw 段評価そのもの。 -/
lemma monicKTracedTripleRawDiagramPasting_generated (n : ℕ) :
    stdSimplex.δ 2 ≫ tripleRawDiagramPastingSecond ≫
        monicKTracedTripleRawDiagramPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedCoherentTripleGeneratedEdge F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleRawDiagramPasting_second, monicKTracedTripleRawSecondTriangle]
  simp only [← Category.assoc, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  all_goals rfl

end SerrePositivity.KST.SConstruction
