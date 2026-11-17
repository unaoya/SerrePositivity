module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TruncationHomology
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionReduction
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionExact
public import SerrePositivity.HomologicalAlgebra.CochainTensor.ShortExact

/-!
# 有限列の完備テンソルの横切断

## 概要
同じ有限反復完備化で、始域と標的の尾部の一様下界を接続する。

## 方針
始域は各次数で分裂する Tot の短完全列をテンソルし、導来完備化の完全性を使う。
標的は加法的な行関手を施した短完全列を使う。

## 規約
複体全体の鎖分裂、係数の有限性、項ごとの有界性は仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の固定次数を有限頭部へ戻す両側の射影。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
variable {R S : Type u} [CommRing R] [CommRing S]
variable {f : R →+* S} (L : ScalarResolution f)

/-- 有限列の完備テンソルを施した実際の尾部の Tot の一様下界。 -/
theorem finiteCompletedTensor_total_tail_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < (N : ℤ) + b - (c : ℤ)) :
    IsZero (((L.finiteCompletedTensorFunctor x).obj (total (RowTruncation.tail K N))).homology q) :=
  L.finiteCompletedTensor_lowerBound x c hf (total (RowTruncation.tail K N))
    ((N : ℤ) + b) (RowTruncation.total_tail_homology_lowerBound K N b hK) q hq

/-- 各行の有限列の完備テンソルを取った実際の尾部の Tot の下界。 -/
theorem total_finiteCompletedTensor_tail_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < (N : ℤ) + b - (c : ℤ)) :
    IsZero ((total (((L.finiteCompletedTensorFunctor x).mapHomologicalComplex (.up ℕ)).obj
      (RowTruncation.tail K N))).homology q) := by
  apply total_tail_lowerBound _ N (b-(c : ℤ))
  · intro n hn
    exact (L.finiteCompletedTensorFunctor x).map_isZero (RowTruncation.tail_isZero K N n hn)
  · intro n hn i hi
    exact L.finiteCompletedTensor_lowerBound x c hf ((RowTruncation.tail K N).X n) b
      (RowTruncation.tail_homology_lowerBound K N b hK n hn) i hi
  · omega

/-- 完備テンソル後の始域でも、深い有限頭部への射影は指定次数で擬同型。 -/
theorem finiteCompletedTensor_total_projection_quasiIsoAt {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q+1 < (N : ℤ) + b - (c : ℤ)) :
    QuasiIsoAt ((L.finiteCompletedTensorFunctor x).map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (RowTruncation.projection K N))) q := by
  let T := (RowTruncation.shortComplex K N).map
    (cochainProductTotalizationFunctor (ModuleCat.{u} R))
  let σ := totalDegreeSplitting (RowTruncation.shortComplex K N)
    (RowTruncation.rowSplitting K N)
  apply finiteCompletion_quasiIsoAt_g_of_left_zero x
    (cochainTensorShortComplexLeft L.complex T)
    (cochainTensorShortComplexLeft_shortExact L.complex T σ) q
  · exact L.finiteCompletedTensor_total_tail_lowerBound x c hf K N b hK q (by omega)
  · exact L.finiteCompletedTensor_total_tail_lowerBound x c hf K N b hK (q+1) hq

/-- 完備テンソルを施した行の Tot でも、深い有限頭部への射影は指定次数で擬同型。 -/
theorem total_finiteCompletedTensor_projection_quasiIsoAt {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q+1 < (N : ℤ) + b - (c : ℤ)) :
    QuasiIsoAt ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (((L.finiteCompletedTensorFunctor x).mapHomologicalComplex (.up ℕ)).map
        (RowTruncation.projection K N))) q := by
  apply total_mapped_projection_quasiIsoAt
  · exact L.total_finiteCompletedTensor_tail_lowerBound x c hf K N b hK q (by omega)
  · exact L.total_finiteCompletedTensor_tail_lowerBound x c hf K N b hK (q+1) hq

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
