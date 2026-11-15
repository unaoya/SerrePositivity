module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TruncationHomology
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletionAdditive

/-!
# 実際の横切断の完備テンソルの尾部の下界

## 概要
元の一様なコホモロジー下界から、主元完備テンソル比較の両側の尾部を評価する。

## 方針
始域では元の尾部の Tot を評価し、標的では各行の完備テンソルを評価してから Tot を取る。

## 規約
主元版の法則である。有限列版の完了はこの補題だけから主張しない。

## 使われ方
BS 著者版 Lemma 4.22 の有限切断の誤差の評価。
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

/-- 主元完備テンソル比較の始域の、実際の横尾部の下界。 -/
theorem completedTensor_total_tail_lowerBound (a : R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f (fun _ : Fin 1 => a) c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < (N : ℤ) + b - (c : ℤ)) :
    IsZero (((L.completedTensorFunctor a).obj (total (RowTruncation.tail K N))).homology q) :=
  L.completedTensor_lowerBound_principal a c hf (total (RowTruncation.tail K N))
    ((N : ℤ) + b) (RowTruncation.total_tail_homology_lowerBound K N b hK) q hq

/-- 主元完備テンソル比較の標的の、実際の横尾部の下界。 -/
theorem total_completedTensor_tail_lowerBound (a : R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f (fun _ : Fin 1 => a) c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < (N : ℤ) + b - (c : ℤ)) :
    IsZero ((total (((L.completedTensorFunctor a).mapHomologicalComplex (.up ℕ)).obj
      (RowTruncation.tail K N))).homology q) := by
  apply total_tail_lowerBound _ N (b-(c : ℤ))
  · intro n hn
    exact (L.completedTensorFunctor a).map_isZero (RowTruncation.tail_isZero K N n hn)
  · intro n hn i hi
    exact L.completedTensor_lowerBound_principal a c hf ((RowTruncation.tail K N).X n) b
      (RowTruncation.tail_homology_lowerBound K N b hK n hn) i hi
  · omega

/-- 主元完備テンソルの各行の Tot では、深い有限頭部への射影は指定次数で擬同型。 -/
theorem total_completedTensor_projection_quasiIsoAt (a : R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f (fun _ : Fin 1 => a) c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q+1 < (N : ℤ) + b - (c : ℤ)) :
    QuasiIsoAt ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (((L.completedTensorFunctor a).mapHomologicalComplex (.up ℕ)).map
        (RowTruncation.projection K N))) q := by
  apply total_mapped_projection_quasiIsoAt
  · exact L.total_completedTensor_tail_lowerBound a c hf K N b hK q (by omega)
  · exact L.total_completedTensor_tail_lowerBound a c hf K N b hK (q+1) hq

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal.ScalarResolution
