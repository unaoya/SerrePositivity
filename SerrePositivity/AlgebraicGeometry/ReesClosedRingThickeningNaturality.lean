module

public import SerrePositivity.AlgebraicGeometry.ReesClosedRingThickeningSemilinear

/-!
概要：Rees の商環表示で、厚化 Frobenius の因子分解と遷移の可換性を示す。
方針：すべての射を同じ代表元の p^e 乗で照合する。
規約：戻す射はイデアル包含による実際の商の因子写像。
使われ方：核の評価・像の安定化へ Frobenius を接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

/-- 厚化から戻した写像は、Rees の実際の商環上の反復 Frobenius。 -/
theorem reesClosedRingThickeningFrobenius_factor (n e : ℕ) :
    (Ideal.Quotient.factor (Ideal.map_mono
      (f := algebraMap R A) (frobeniusThickeningPower_le I p hp n e))).comp
      (reesClosedRingThickeningFrobenius I p hp hA n e) =
    frobeniusDirectSystemMap (A ⧸ (I ^ n).map (algebraMap R A)) p hp
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) 0 e (Nat.zero_le e) := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, reesClosedRingThickeningFrobenius_mk,
    Ideal.Quotient.factor_mk, frobeniusDirectSystemMap_apply, Nat.sub_zero, map_pow]

/-- 厚化 Frobenius は、実際の商環の厚さを下げる遷移と可換。 -/
theorem reesClosedRingThickeningFrobenius_transition (n m e : ℕ) (hmn : m ≤ n) :
    (Ideal.Quotient.factor (Ideal.map_mono (f := algebraMap R A)
      (Ideal.pow_le_pow_right (Nat.mul_le_mul_left (p ^ e) hmn)))).comp
      (reesClosedRingThickeningFrobenius I p hp hA n e) =
    (reesClosedRingThickeningFrobenius I p hp hA m e).comp
      (Ideal.Quotient.factor (Ideal.map_mono (f := algebraMap R A)
        (Ideal.pow_le_pow_right hmn))) := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk, reesClosedRingThickeningFrobenius_mk]

end SerrePositivity.AlgebraicGeometry
