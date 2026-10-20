module
public import SerrePositivity.KST.SConstruction.OuterPastingFaceEquations
public import SerrePositivity.KST.SConstruction.TracedTripleSharedDirectRealizationPasting

/-! # 元の raw BF 二面を貼る共有頂点
概要：右 BF 比較辺と第一 whisker の接合点、両 whisker の共通終点を厳密に同定する。
方針：既存の全対角辺の等号と正規化円柱の全境界固定を頂点へ制限する。
規約：同じ実複体内の零単体写像の等号を使い、写像先での一致に留めない。
使われ方：元の BF 二面全体を内ホーンと外ホーンへ順に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 右外側 BF 比較辺は、元の後二射段上辺と同じ接合点を共有する。 -/
lemma outerStagePasting_right_whisker_corner :
    stdSimplex.δ 0 ≫ stdSimplex.δ 0 ≫ outerStagePastingRightCell.{u} =
      stdSimplex.δ 1 ≫ stdSimplex.δ 0 ≫ triangleDiagonalPastingFirst ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal ≫
          correctionNormalizationPastingOriginal ≫ outerBinaryPastingOriginal ≫
            outerStagePastingOriginal := by
  have he : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
    stdSimplex.δ_comp_δ_self (i := (0 : Fin 2))
  have hm : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k; rfl
  have hb := boundaryEdgeEndpoint correctionNormalizationPastingRightTarget
    (correctionNormalizationRightEdge ≫ correctionNormalizationPastingOriginal)
    correctionNormalizationPastingRightTarget_boundary (0 : Fin 2)
  calc
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ outerStagePastingRightCell := by
      simp only [← Category.assoc]
      rw [he]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ outerBinaryPastingRightCell ≫
        outerStagePastingOriginal := by rw [outerStagePasting_right_diagonal]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 0 ≫ outerBinaryPastingRightCell ≫
        outerStagePastingOriginal := by
      simp only [← Category.assoc]
      rw [he]
    _ = stdSimplex.δ 0 ≫ correctionNormalizationPastingRightTarget ≫
        outerBinaryPastingOriginal ≫ outerStagePastingOriginal := by
      simpa only [Category.assoc] using
        congrArg (fun q => stdSimplex.δ (0 : Fin 2) ≫ q ≫ outerStagePastingOriginal)
          outerBinaryPasting_right_second.{u}
    _ = stdSimplex.δ 0 ≫ correctionNormalizationRightEdge ≫
        correctionNormalizationPastingOriginal ≫ outerBinaryPastingOriginal ≫
          outerStagePastingOriginal := by
      simpa only [Category.assoc] using
        congrArg (· ≫ outerBinaryPastingOriginal ≫ outerStagePastingOriginal) hb
    _ = _ := by
      unfold correctionNormalizationRightEdge
      simp only [← Category.assoc]
      rw [hm]

/-- 元の両 whisker の終点は六面複体内で既に同じ零単体。 -/
lemma correctionInterchangePasting_whisker_target :
    stdSimplex.δ 0 ≫ stdSimplex.δ 0 ≫ triangleDiagonalPastingFirst ≫
        doubleDiagonalTrianglePastingSecond.{u} 0 2 ≫ correctionInterchangePastingOriginal =
      stdSimplex.δ 0 ≫ stdSimplex.δ 0 ≫ correctionInterchangePastingFirst := by
  have he : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
    stdSimplex.δ_comp_δ_self (i := (0 : Fin 2))
  calc
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ triangleDiagonalPastingFirst ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal := by
      simp only [← Category.assoc]
      rw [he]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal := by
      simpa only [Category.assoc] using
        congrArg (fun q => stdSimplex.δ (0 : Fin 2) ≫ q ≫
          doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal)
            triangleDiagonalPasting_shared.{u}
    _ = stdSimplex.δ 0 ≫ correctionPastingUpper ≫
        correctionInterchangePastingOriginal := by
      unfold correctionPastingUpper
      simp only [← Category.assoc]
      rw [he]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 0 ≫ correctionInterchangePastingSecond := by
      rw [correctionInterchangePasting_upper]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ correctionInterchangePastingSecond := by
      simp only [← Category.assoc]
      rw [he]
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ correctionInterchangePastingFirst := by
      rw [correctionInterchangePasting_diagonal]
    _ = _ := by
      simp only [← Category.assoc]
      rw [he]

/-- 第一 BF 三角形の二入力辺を、既存の全高次比較複体内に置く。 -/
def tripleRawFirstLower : (Δ[1] : SSet.{u}) ⟶ tripleSharedDirectRealizationPasting :=
  stdSimplex.δ 0 ≫ outerStagePastingRightCell ≫ tripleSharedDirectPastingOriginal ≫
    tripleSharedDirectRealizationPastingOriginal

/-- 第一 BF 三角形の第二辺は元の同じ第一 whisker。 -/
def tripleRawFirstUpper : (Δ[1] : SSet.{u}) ⟶ tripleSharedDirectRealizationPasting :=
  tripleSharedDirectFirstWhisker ≫ tripleSharedDirectRealizationPastingOriginal

/-- 第二 BF 三角形の上辺も元の同じ第二 whisker。 -/
def tripleRawSecondUpper : (Δ[1] : SSet.{u}) ⟶ tripleSharedDirectRealizationPasting :=
  tripleSharedDirectSecondWhisker ≫ tripleSharedDirectRealizationPastingOriginal

/-- 第一全三角形を貼る内ホーンの接合点は実複体内で厳密に一致する。 -/
lemma tripleRawFirst_corner :
    stdSimplex.δ 0 ≫ tripleRawFirstLower.{u} =
      stdSimplex.δ 1 ≫ tripleRawFirstUpper := by
  simpa only [tripleRawFirstLower, tripleRawFirstUpper, tripleSharedDirectFirstWhisker,
    Category.assoc] using
    congrArg (· ≫ tripleSharedDirectPastingOriginal ≫
      tripleSharedDirectRealizationPastingOriginal) outerStagePasting_right_whisker_corner.{u}

/-- 両 BF whisker は同じ全高次比較複体内で終点を厳密に共有する。 -/
lemma tripleRawWhiskers_target :
    stdSimplex.δ 0 ≫ tripleRawFirstUpper.{u} =
      stdSimplex.δ 0 ≫ tripleRawSecondUpper := by
  simpa only [tripleRawFirstUpper, tripleRawSecondUpper, tripleSharedDirectFirstWhisker,
    tripleSharedDirectSecondWhisker, Category.assoc] using
    congrArg (· ≫ correctionNormalizationPastingOriginal ≫ outerBinaryPastingOriginal ≫
      outerStagePastingOriginal ≫ tripleSharedDirectPastingOriginal ≫
        tripleSharedDirectRealizationPastingOriginal)
      correctionInterchangePasting_whisker_target.{u}

end SerrePositivity.KST.SConstruction
