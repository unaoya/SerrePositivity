module
public import SerrePositivity.KST.SConstruction.CorrectionNormalizationPasting
public import SerrePositivity.KST.SConstruction.InterchangePastingHornFaces
public import SerrePositivity.KST.SConstruction.BoundaryEdgeEndpoints

/-! # 外側二部分面の共有頂点を同じ実複体内で回収する
概要：正規化出口と隣接する元の全辺が、同じ中間頂点を共有することを証明する。
方針：元の貼り合わせ面の恒等式と、出口の全境界固定式を組み合わせる。
規約：実複体内の全零単体写像の厳密等号であり、写像先だけの一致にしない。
使われ方：元の両外側二部分三角形全体を同じ二つの全内ホーンへ貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 左外側の第二辺となる、元の交換第一面の全下面。 -/
def correctionOuterLeftSecond : (Δ[1] : SSet.{u}) ⟶ correctionNormalizationPasting :=
  stdSimplex.δ 2 ≫ correctionInterchangePastingFirst ≫ correctionNormalizationPastingOriginal

/-- 右外側の第一辺となる、元の最初の全補正辺。 -/
def correctionOuterRightFirst : (Δ[1] : SSet.{u}) ⟶ correctionNormalizationPasting :=
  stdSimplex.δ 2 ≫ triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫
    correctionInterchangePastingOriginal ≫ correctionNormalizationPastingOriginal

/-- 元の左補正辺と交換第一下面は、六面複体内で同じ中間頂点を共有する。 -/
lemma correctionOuterLeft_base_corner :
    stdSimplex.δ 0 ≫ correctionNormalizationLeftEdge.{u} =
      stdSimplex.δ 1 ≫ stdSimplex.δ 2 ≫ correctionInterchangePastingFirst := by
  have hm : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro k
    fin_cases k; rfl
  have hs : stdSimplex.δ.{u} (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    simpa using stdSimplex.δ_comp_δ_self (i := (1 : Fin 2))
  calc
    _ = stdSimplex.δ 1 ≫ correctionPastingLower ≫ correctionInterchangePastingOriginal := by
      unfold correctionNormalizationLeftEdge correctionPastingLower
      simp only [← Category.assoc]
      rw [hm]
    _ = stdSimplex.δ 1 ≫ stdSimplex.δ 2 ≫ correctionInterchangePastingSecond := by
      rw [correctionInterchangePasting_lower]
    _ = stdSimplex.δ 1 ≫ stdSimplex.δ 1 ≫ correctionInterchangePastingSecond := by
      simp only [← Category.assoc]
      rw [hs]
    _ = stdSimplex.δ 1 ≫ stdSimplex.δ 1 ≫ correctionInterchangePastingFirst := by
      simpa only [Category.assoc] using
        congrArg (stdSimplex.δ (1 : Fin 2) ≫ ·) correctionInterchangePasting_diagonal.{u}
    _ = _ := by
      simp only [← Category.assoc]
      rw [hs]

/-- 元の最初の補正辺と右補正辺は、六面複体内で同じ中間頂点を共有する。 -/
lemma correctionOuterRight_base_corner :
    stdSimplex.δ 0 ≫ stdSimplex.δ 2 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingFirst.{u} 0 2 ≫ correctionInterchangePastingOriginal =
      stdSimplex.δ 1 ≫ correctionNormalizationRightEdge := by
  have hm : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro k
    fin_cases k; rfl
  have hs : stdSimplex.δ.{u} (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    simpa using stdSimplex.δ_comp_δ_self (i := (1 : Fin 2))
  calc
    _ = stdSimplex.δ 1 ≫ stdSimplex.δ 0 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingFirst 0 2 ≫ correctionInterchangePastingOriginal := by
      simp only [← Category.assoc]
      rw [hm]
    _ = stdSimplex.δ 1 ≫ stdSimplex.δ 2 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal := by
      simpa only [Category.assoc] using
        congrArg (fun q => stdSimplex.δ (1 : Fin 2) ≫ q ≫ correctionInterchangePastingOriginal)
          (doubleDiagonalTrianglePasting_shared.{u} 0 2)
    _ = stdSimplex.δ 1 ≫ stdSimplex.δ 1 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal := by
      simp only [← Category.assoc]
      rw [hs]
    _ = stdSimplex.δ 1 ≫ stdSimplex.δ 1 ≫ triangleDiagonalPastingFirst ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal := by
      simpa only [Category.assoc] using
        congrArg (fun q => stdSimplex.δ (1 : Fin 2) ≫ q ≫
          doubleDiagonalTrianglePastingSecond 0 2 ≫ correctionInterchangePastingOriginal)
            triangleDiagonalPasting_shared.{u}.symm
    _ = _ := by
      unfold correctionNormalizationRightEdge
      simp only [← Category.assoc]
      rw [hs]

/-- 左正規化出口も、元の隣接辺と複体内で同じ中間頂点を厳密に共有する。 -/
lemma correctionOuterLeft_corner :
    stdSimplex.δ 0 ≫ correctionNormalizationPastingLeftTarget.{u} =
      stdSimplex.δ 1 ≫ correctionOuterLeftSecond := by
  have he := boundaryEdgeEndpoint correctionNormalizationPastingLeftTarget
    (correctionNormalizationLeftEdge ≫ correctionNormalizationPastingOriginal)
    correctionNormalizationPastingLeftTarget_boundary (0 : Fin 2)
  exact he.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ correctionNormalizationPastingOriginal)
      correctionOuterLeft_base_corner.{u}).trans (by
        simp only [correctionOuterLeftSecond, Category.assoc])))

/-- 右正規化出口も、元の最初の全補正辺と同じ中間頂点を厳密に共有する。 -/
lemma correctionOuterRight_corner :
    stdSimplex.δ 0 ≫ correctionOuterRightFirst.{u} =
      stdSimplex.δ 1 ≫ correctionNormalizationPastingRightTarget := by
  have he := boundaryEdgeEndpoint correctionNormalizationPastingRightTarget
    (correctionNormalizationRightEdge ≫ correctionNormalizationPastingOriginal)
    correctionNormalizationPastingRightTarget_boundary (1 : Fin 2)
  calc
    _ = (stdSimplex.δ 1 ≫ correctionNormalizationRightEdge) ≫
        correctionNormalizationPastingOriginal := by
      simpa only [correctionOuterRightFirst, Category.assoc] using
        congrArg (· ≫ correctionNormalizationPastingOriginal) correctionOuterRight_base_corner.{u}
    _ = _ := (Category.assoc _ _ _).trans he.symm

end SerrePositivity.KST.SConstruction
