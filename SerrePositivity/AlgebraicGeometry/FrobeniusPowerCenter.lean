module

public import SerrePositivity.AlgebraicGeometry.FrobeniusQuotientFactor
public import SerrePositivity.AlgebraicGeometry.SurjectiveSpectrumRadical

/-!
概要：中心の正の冪とその拡大の逆像を Frobenius 順極限で比較する。
方針：Spec 全射性による根基の等式を、実際の商の因子写像に適用する。
規約：指数は正。中心をその根基で置き換えて定義し直さない。
使われ方：導手の中心と指定した中心を同じ冪の商を経由して比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 正の冪による商から元の中心による商への実際の射は、Frobenius 順極限で全単射。 -/
theorem frobeniusPowerCenter_bijective (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (I : Ideal A) (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective (frobeniusDirectLimitMap p hp
      (frobeniusQuotientPrimeCast p hA (I ^ n)) (frobeniusQuotientPrimeCast p hA I)
      (Ideal.Quotient.factor (Ideal.pow_le_self hn))) := by
  apply frobeniusQuotientFactor_bijective p hp hA
  rw [Ideal.radical_pow I hn]
  exact Ideal.le_radical

/-- Spec 全射なら、拡大した正の冪の逆像はその冪の根基に含まれる。 -/
theorem surjectiveSpectrum_comap_map_pow_le_radical (f : A →+* B)
    (hs : Function.Surjective (PrimeSpectrum.comap f)) (I : Ideal A) (n : ℕ) :
    ((I ^ n).map f).comap f ≤ (I ^ n).radical := by
  rw [← surjectiveSpectrum_radical_comap_map f hs (I ^ n)]
  exact Ideal.le_radical

/-- Spec 全射なら、冪の商から拡大の逆像の商への因子写像は Frobenius 順極限で全単射。 -/
theorem frobeniusContractedPowerCenter_bijective
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (f : A →+* B) (hs : Function.Surjective (PrimeSpectrum.comap f))
    (I : Ideal A) (n : ℕ) :
    Function.Bijective (frobeniusDirectLimitMap p hp
      (frobeniusQuotientPrimeCast p hA (I ^ n))
      (frobeniusQuotientPrimeCast p hA (((I ^ n).map f).comap f))
      (Ideal.Quotient.factor Ideal.le_comap_map)) := by
  exact frobeniusQuotientFactor_bijective p hp hA Ideal.le_comap_map
    (surjectiveSpectrum_comap_map_pow_le_radical f hs I n)

end SerrePositivity.AlgebraicGeometry
