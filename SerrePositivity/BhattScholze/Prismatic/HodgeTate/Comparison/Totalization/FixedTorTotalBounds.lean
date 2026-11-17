module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FixedTorBounds
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.LowerBound
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorComponents

/-!
# 行ごとの完全 Tor 振幅と積全複体の下界

## 概要
固定係数模型と有限 Koszul 簡約を各行へ施した積全複体の下界を評価する。

## 方針
既存の完全 Tor 条件を各行へ適用し、対角線の原始元の構成へ渡す。

## 規約
Koszul と全複体の可換性や底変換との可換性は、この補題の前提にも結論にも含めない。

## 使われ方
BS 著者版 Lemma 4.22 の、底変換後の横切断の尾部に対する一様評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 行ごとのテンソル模型へ、同じ有限 Koszul 関手を施した二重複体。 -/
abbrev koszulTensorRows {f : R →+* S} (L : ScalarResolution f)
    {r : ℕ} (x : Fin r → R) (K : CochainComplex (Complex R) ℕ) :
    CochainComplex (Complex R) ℕ :=
  ((koszulFunctor x).mapHomologicalComplex (.up ℕ)).obj (tensorRows L.complex K)

namespace ScalarResolution

variable {f : R →+* S} (L : ScalarResolution f)

/-- 各行の下界と完全 Tor 振幅から、行簡約した全複体の対角線の下界を得る。 -/
theorem koszulTensorRows_total_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℕ → ℤ) (d : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b n → IsZero ((K.X n).homology i))
    (hd : ∀ n : ℕ, d ≤ (n : ℤ) + b n - (c : ℤ)) (q : ℤ) (hq : q < d) :
    IsZero ((total (koszulTensorRows L x K)).homology q) := by
  apply total_homology_isZero_of_diagonal
  intro n
  exact L.koszul_lowerBound x c hf (K.X n) (b n) (hK n) (q - n)
    (by have := hd n; omega)

/-- 一様な行の下界は、完全 Tor 上界だけ下げて積全複体へ渡る。 -/
theorem koszulTensorRows_total_lowerBound_uniform {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i))
    (q : ℤ) (hq : q < b - (c : ℤ)) :
    IsZero ((total (koszulTensorRows L x K)).homology q) :=
  L.koszulTensorRows_total_lowerBound x c hf K (fun _ => b) (b - (c : ℤ)) hK
    (fun n => by omega) q hq

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
