module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FixedTorTotalBounds

/-!
# 横切断の尾部の積全複体の下界

## 概要
最初の N 行が零の二重複体では、一様な縦の下界が全次数で N だけ上がる。

## 方針
低い行の零性と、高い行の対角線の完全性を分ける。完全 Tor の後も同じ議論を使う。

## 規約
尾部の零行以外について、複体の項の零性を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の有限切断による誤差の一様な評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 低い行が零なら、積全複体の下界は横次数だけ上がる。 -/
theorem total_tail_lowerBound (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hzero : ∀ n : ℕ, n < N → IsZero (K.X n))
    (hrow : ∀ n : ℕ, N ≤ n → ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < (N : ℤ) + b) : IsZero ((total K).homology q) := by
  apply total_homology_isZero_of_diagonal
  intro n
  by_cases hn : n < N
  · exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (q - n)).map_isZero (hzero n hn)
  · exact hrow n (by omega) (q - n) (by omega)

namespace ScalarResolution

variable {f : R →+* S} (L : ScalarResolution f)

/-- 完全 Tor 上界 c の後の尾部は、全次数 N+b-c より下で零である。 -/
theorem koszulTensorRows_tail_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ) (b : ℤ)
    (hzero : ∀ n : ℕ, n < N → IsZero (K.X n))
    (hrow : ∀ n : ℕ, N ≤ n → ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < (N : ℤ) + b - (c : ℤ)) :
    IsZero ((total (koszulTensorRows L x K)).homology q) := by
  apply total_tail_lowerBound (koszulTensorRows L x K) N (b - (c : ℤ))
  · intro n hn
    exact (L.tensorFunctor ⋙ koszulFunctor x).map_isZero (hzero n hn)
  · intro n hn i hi
    exact L.koszul_lowerBound x c hf (K.X n) b (hrow n hn) i hi
  · omega

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
