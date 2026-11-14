module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitInvariance

/-!
概要：商環の反復 Frobenius を、より厚い I 進閉厚化を経由させる。
方針：Iⁿ の元の p^e 乗は I^(p^e*n) に入り、商の普遍性を使える。
規約：零環も許し、標数の条件は p の像が零であることだけ。
使われ方：BST13 Lemma 3.9 の核の評価と像の安定化への入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A : Type u} [CommRing A] (I : Ideal A)
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

/-- n から p^e*n への反復 Frobenius の、実際の商環の写像。 -/
def frobeniusThickeningMap (n e : ℕ) : A ⧸ I ^ n →+* A ⧸ I ^ (p ^ e * n) :=
  Ideal.Quotient.lift (I ^ n)
    ((Ideal.Quotient.mk (I ^ (p ^ e * n))).comp
      (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e))) (by
    intro a ha
    rw [RingHom.comp_apply, frobeniusDirectSystemMap_apply, Nat.sub_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [← pow_mul, Nat.mul_comm] using Ideal.pow_mem_pow ha (p ^ e))

/-- 厚化を経由する写像は、代表元を p^e 乗に送る。 -/
theorem frobeniusThickeningMap_mk (n e : ℕ) (a : A) :
    frobeniusThickeningMap I p hp hA n e (Ideal.Quotient.mk (I ^ n) a) =
      Ideal.Quotient.mk (I ^ (p ^ e * n)) (a ^ (p ^ e)) := by
  change Ideal.Quotient.mk _ (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e) a) = _
  rw [frobeniusDirectSystemMap_apply, Nat.sub_zero]

include hp in
/-- 厚い段から元の段へ戻るためのイデアルの包含。 -/
theorem frobeniusThickeningPower_le (n e : ℕ) : I ^ (p ^ e * n) ≤ I ^ n :=
  Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n (pow_pos hp.pos e))

/-- 厚化を経由して元の商へ戻すと、その商の反復 Frobenius そのものになる。 -/
theorem frobeniusThickeningMap_factor (n e : ℕ) :
    (Ideal.Quotient.factor (frobeniusThickeningPower_le I p hp n e)).comp
      (frobeniusThickeningMap I p hp hA n e) =
    frobeniusDirectSystemMap (A ⧸ I ^ n) p hp
      (frobeniusQuotientPrimeCast p hA (I ^ n)) 0 e (Nat.zero_le e) := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, frobeniusThickeningMap_mk,
    Ideal.Quotient.factor_mk, frobeniusDirectSystemMap_apply, Nat.sub_zero, map_pow]

/-- 元の環から厚化への写像と反復 Frobenius の可換性。 -/
theorem frobeniusThickeningMap_projection (n e : ℕ) :
    (frobeniusThickeningMap I p hp hA n e).comp (Ideal.Quotient.mk (I ^ n)) =
      (Ideal.Quotient.mk (I ^ (p ^ e * n))).comp
        (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e)) := rfl

/-- 厚化を経由する反復 Frobenius は、厚さを下げる遷移と可換。 -/
theorem frobeniusThickeningMap_transition (n m e : ℕ) (hmn : m ≤ n) :
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.mul_le_mul_left (p ^ e) hmn))).comp
      (frobeniusThickeningMap I p hp hA n e) =
    (frobeniusThickeningMap I p hp hA m e).comp
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk, frobeniusThickeningMap_mk]

end SerrePositivity.AlgebraicGeometry
