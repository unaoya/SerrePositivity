module
public import SerrePositivity.KST.SConstruction.TripleRawDiagramFaces
public import Mathlib.Algebra.Group.Basic

/-! # 元の十二面が与える共通辺路の消去
概要：全三角形の合成式と三つの全円柱の辺の等値から、指定第四辺の値を検出する。
方針：六組の共有対角面を同じ群で計算し、共有直接辺と第二 whisker を消去する。
規約：全十二面の像を使う計算補題であり、実比較円柱の構成とは区別する。
使われ方：Kan 基点表示に適用して元の指定辺と生成辺の同じ類を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 六組の実三角形が与える辺路の関係から、共通の始辺と終辺を消去する。 -/
lemma sixDiamondCancellation {G : Type v} [Group G]
    (p q a b k₁ k₂ k₃ l r e x y s t : G)
    (h₁ : q * p = k₂ * k₁) (h₂ : e * a = k₃ * k₂)
    (h₃ : r * l = k₃ * q) (h₄ : x * s = l * p)
    (h₅ : b * t = a * k₁) (h₆ : r * y = e * b) (hs : s = t) : x = y := by
  suffices h : r * x * t = r * y * t from
    mul_left_cancel (mul_right_cancel h)
  calc
    r * x * t = r * (x * s) := by rw [hs, mul_assoc]
    _ = r * (l * p) := by rw [h₄]
    _ = k₃ * (q * p) := by rw [← mul_assoc, h₃, mul_assoc]
    _ = (k₃ * k₂) * k₁ := by rw [h₁, ← mul_assoc]
    _ = e * (a * k₁) := by rw [← h₂, mul_assoc]
    _ = e * (b * t) := by rw [← h₅]
    _ = (r * y) * t := by rw [← mul_assoc, ← h₆]

/-- 全十二面を保持した実複体内で、元の二つの第四辺の群値は等しい。 -/
lemma tripleRawDiagramPasting_value {G : Type v} [Group G]
    (V : ((Δ[1] : SSet.{u}) ⟶ tripleRawDiagramPasting) → G)
    (ht : ∀ T : (Δ[2] : SSet.{u}) ⟶ tripleRawDiagramPasting,
      V (stdSimplex.δ 1 ≫ T) = V (stdSimplex.δ 0 ≫ T) * V (stdSimplex.δ 2 ≫ T))
    (hnl : V (correctionNormalizationPastingLeftTarget ≫ outerBinaryPastingOriginal ≫
        outerStagePastingOriginal ≫ tripleSharedDirectPastingOriginal ≫
          tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal) =
      V (correctionNormalizationLeftEdge ≫ correctionNormalizationPastingOriginal ≫
        outerBinaryPastingOriginal ≫ outerStagePastingOriginal ≫
          tripleSharedDirectPastingOriginal ≫ tripleSharedDirectRealizationPastingOriginal ≫
            tripleRawDiagramPastingOriginal))
    (hnr : V (correctionNormalizationPastingRightTarget ≫ outerBinaryPastingOriginal ≫
        outerStagePastingOriginal ≫ tripleSharedDirectPastingOriginal ≫
          tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal) =
      V (correctionNormalizationRightEdge ≫ correctionNormalizationPastingOriginal ≫
        outerBinaryPastingOriginal ≫ outerStagePastingOriginal ≫
          tripleSharedDirectPastingOriginal ≫ tripleSharedDirectRealizationPastingOriginal ≫
            tripleRawDiagramPastingOriginal))
    (hs : V (stdSimplex.δ 2 ≫ outerStagePastingLeftCell ≫ tripleSharedDirectPastingOriginal ≫
        tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal) =
      V (stdSimplex.δ 2 ≫ outerStagePastingRightCell ≫ tripleSharedDirectPastingOriginal ≫
        tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal)) :
    V (stdSimplex.δ 0 ≫ outerStagePastingLeftCell ≫ tripleSharedDirectPastingOriginal ≫
        tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal) =
      V (stdSimplex.δ 2 ≫ tripleRawDiagramPastingSecond) := by
  let O := tripleSharedDirectPastingOriginal.{u} ≫
    tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal
  let N := outerBinaryPastingOriginal.{u} ≫ outerStagePastingOriginal ≫ O
  let J := correctionNormalizationPastingOriginal.{u} ≫ N
  let D := correctionInterchangePastingOriginal.{u} ≫ J
  have diamond (T U : (Δ[2] : SSet.{u}) ⟶ tripleRawDiagramPasting)
      (hd : stdSimplex.δ 1 ≫ T = stdSimplex.δ 1 ≫ U) :
      V (stdSimplex.δ 0 ≫ T) * V (stdSimplex.δ 2 ≫ T) =
        V (stdSimplex.δ 0 ≫ U) * V (stdSimplex.δ 2 ≫ U) :=
    (ht T).symm.trans ((congrArg V hd).trans (ht U))
  have hdA := congrArg (fun k => k ≫ doubleDiagonalTrianglePastingFirst.{u} 0 2 ≫ D)
    triangleDiagonalPasting_shared.{u}
  have hdB := congrArg (fun k => k ≫ doubleDiagonalTrianglePastingSecond.{u} 0 2 ≫ D)
    triangleDiagonalPasting_shared.{u}
  simp only [Category.assoc] at hdA hdB
  have hA := diamond
    (triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫ D)
    (triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫ D) hdA
  have hB := diamond
    (triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫ D)
    (triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫ D) hdB
  have hmid := congrArg (fun k => k ≫ D) (doubleDiagonalTrianglePasting_shared.{u} 0 2)
  simp only [Category.assoc] at hmid
  rw [← hmid] at hB
  have hI := diamond (correctionInterchangePastingFirst ≫ J)
    (correctionInterchangePastingSecond ≫ J)
    (by simpa only [Category.assoc] using
      congrArg (· ≫ J) correctionInterchangePasting_diagonal.{u}.symm)
  simp only [← Category.assoc] at hI
  rw [← correctionInterchangePasting_lower, ← correctionInterchangePasting_upper] at hI
  simp only [correctionPastingLower, correctionPastingUpper, Category.assoc] at hI
  have hL := diamond (outerStagePastingLeftCell ≫ O)
    (outerBinaryPastingLeftCell ≫ outerStagePastingOriginal ≫ O)
    (by simpa only [Category.assoc] using
      congrArg (· ≫ O) outerStagePasting_left_diagonal.{u})
  have hR := diamond (outerStagePastingRightCell ≫ O)
    (outerBinaryPastingRightCell ≫ outerStagePastingOriginal ≫ O)
    (by simpa only [Category.assoc] using
      congrArg (· ≫ O) outerStagePasting_right_diagonal.{u})
  simp only [← Category.assoc] at hL hR
  rw [outerBinaryPasting_left_first, outerBinaryPasting_left_second] at hL
  rw [outerBinaryPasting_right_first, outerBinaryPasting_right_second] at hR
  simp only [Category.assoc] at hL hR
  change V (stdSimplex.δ 0 ≫ outerStagePastingLeftCell ≫ O) *
      V (stdSimplex.δ 2 ≫ outerStagePastingLeftCell ≫ O) =
    V (stdSimplex.δ 2 ≫ correctionInterchangePastingFirst ≫ J) *
      V (correctionNormalizationPastingLeftTarget ≫ N) at hL
  change V (stdSimplex.δ 0 ≫ outerStagePastingRightCell ≫ O) *
      V (stdSimplex.δ 2 ≫ outerStagePastingRightCell ≫ O) =
    V (correctionNormalizationPastingRightTarget ≫ N) *
      V (stdSimplex.δ 2 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingFirst 0 2 ≫ D) at hR
  change V (correctionNormalizationPastingLeftTarget ≫ N) =
    V (correctionNormalizationLeftEdge ≫ J) at hnl
  change V (correctionNormalizationPastingRightTarget ≫ N) =
    V (correctionNormalizationRightEdge ≫ J) at hnr
  rw [hnl] at hL
  rw [hnr] at hR
  simp only [correctionNormalizationLeftEdge, correctionNormalizationRightEdge,
    Category.assoc] at hL hR
  have hBF := diamond tripleRawDiagramPastingSecond tripleRawDiagramPastingFirst
    tripleRawDiagramPasting_diagonal.symm
  rw [tripleRawDiagramPasting_second_upper, tripleRawDiagramPasting_first_upper,
    tripleRawDiagramPasting_first_lower] at hBF
  simp only [tripleRawSecondUpper, tripleRawFirstUpper, tripleRawFirstLower,
    tripleSharedDirectSecondWhisker, tripleSharedDirectFirstWhisker, Category.assoc] at hBF
  exact sixDiamondCancellation _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hI hL hR hBF hs

end SerrePositivity.KST.SConstruction
