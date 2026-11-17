module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.RowTruncationExact
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TotalSplitExact
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# 横切断の射影が誘導する指定次数の擬同型

## 概要
尾部の隣接する二次数のホモロジーが零なら、有限頭部への射影はその次数で擬同型となる。

## 方針
横切断の各行の分裂を Tot に渡し、短完全列の長完全列を使う。

## 規約
入力の内部次数を項ごとには切り詰めない。

## 使われ方
BS 著者版 Lemma 4.22 の、固定次数を有限頭部へ帰着する手順。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 短完全列の第一項の隣接二次数が零なら、第二射はその次数で擬同型である。 -/
theorem quasiIsoAt_g_of_left_homology_zero (S : ShortComplex (Complex R))
    (hS : S.ShortExact) (q : ℤ)
    (hq : IsZero (S.X₁.homology q)) (hq1 : IsZero (S.X₁.homology (q+1))) :
    QuasiIsoAt S.g q := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  haveI : Mono (homologyMap S.g q) :=
    (hS.homology_exact₂ q).mono_g (hq.eq_zero_of_src _)
  haveI : Epi (homologyMap S.g q) :=
    (hS.homology_exact₃ q (q+1) rfl).epi_f (hq1.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- 加法的な行関手を施した横切断は、指定 Tot の短完全列を与える。 -/
theorem total_mapped_truncation_shortExact (F : Complex R ⥤ Complex R) [F.Additive]
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) :
    (((RowTruncation.shortComplex K N).map (F.mapHomologicalComplex (.up ℕ))).map
      (cochainProductTotalizationFunctor (ModuleCat.{u} R))).ShortExact := by
  apply total_shortExact_of_rowSplitting
  intro n
  exact (RowTruncation.rowSplitting K N n).map F

/-- 行関手を施した尾部の二次数が消えれば、同じ Tot の頭部射影はその次数で擬同型。 -/
theorem total_mapped_projection_quasiIsoAt (F : Complex R ⥤ Complex R) [F.Additive]
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (q : ℤ)
    (hq : IsZero ((total ((F.mapHomologicalComplex (.up ℕ)).obj
      (RowTruncation.tail K N))).homology q))
    (hq1 : IsZero ((total ((F.mapHomologicalComplex (.up ℕ)).obj
      (RowTruncation.tail K N))).homology (q+1))) :
    QuasiIsoAt ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      ((F.mapHomologicalComplex (.up ℕ)).map (RowTruncation.projection K N))) q :=
  quasiIsoAt_g_of_left_homology_zero _ (total_mapped_truncation_shortExact F K N) q hq hq1

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
