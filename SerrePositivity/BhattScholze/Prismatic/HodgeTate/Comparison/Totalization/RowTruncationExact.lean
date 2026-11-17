module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NaturalTruncation
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# 横切断の短完全列

## 概要
横次数の尾部・元の図式・有限頭部からなる短完全列を、各行の分裂で確認する。

## 方針
一つの行では、包含または射影のどちらかが元の行の指定同型になる。

## 規約
横次数での分裂を複体全体の鎖分裂とは主張しない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部と尾部の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.RowTruncation
variable {R : Type u} [CommRing R]
variable (K : CochainComplex (Complex R) ℕ) (N : ℕ)

/-- 尾部の包含の後の有限頭部への射影は零。 -/
theorem inclusion_projection : inclusion K N ≫ projection K N = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (inclusion K N).f n ≫ (projection K N).f n = 0
  by_cases h : N ≤ n
  · exact (head_isZero K N n h).eq_of_tgt _ _
  · exact (tail_isZero K N n (by omega)).eq_of_src _ _

/-- 尾部の包含と有限頭部への射影からなる、元の短複体。 -/
def shortComplex : ShortComplex (CochainComplex (Complex R) ℕ) :=
  ShortComplex.mk (inclusion K N) (projection K N) (inclusion_projection K N)

/-- 残る行では、尾部の包含は指定行同型そのものである。 -/
theorem inclusion_f_isIso (n : ℕ) (h : N ≤ n) : IsIso ((inclusion K N).f n) := by
  change IsIso (if h : N ≤ n then (tailXIso K N n h).hom else 0)
  rw [dif_pos h]
  infer_instance

/-- 残る行では、有限頭部への射影は指定行同型そのものである。 -/
theorem projection_f_isIso (n : ℕ) (h : n < N) : IsIso ((projection K N).f n) := by
  change IsIso (if h : n < N then (headXIso K N n h).inv else 0)
  rw [dif_pos h]
  infer_instance

/-- 横次数ごとの分裂。これは内部次数の全複体の鎖分裂である。 -/
def rowSplitting (n : ℕ) :
    ((shortComplex K N).map (HomologicalComplex.eval (Complex R) (.up ℕ) n)).Splitting := by
  by_cases h : N ≤ n
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (inclusion_f_isIso K N n h)
      (head_isZero K N n h)
  · exact ShortComplex.Splitting.ofIsZeroOfIsIso _ (tail_isZero K N n (by omega))
      (projection_f_isIso K N n (by omega))

/-- 横切断の短複体は、実際に短完全である。 -/
theorem shortComplex_shortExact : (shortComplex K N).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => (rowSplitting K N n).shortExact)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.RowTruncation
