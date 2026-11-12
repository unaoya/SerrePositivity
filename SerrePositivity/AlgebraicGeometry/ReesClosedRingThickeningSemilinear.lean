module

public import SerrePositivity.AlgebraicGeometry.ReesClosedRingThickeningFrobenius

/-!
概要：閉厚化を経由する反復 Frobenius の係数半線形性を明示する。
方針：スカラーの代表元と p^e 乗を照合し、環の写像を半線形写像にする。
規約：係数の Frobenius も零環を許す実際の反復写像。
使われ方：斉次局所化と Čech の係数図式への接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 閉厚化の反復 Frobenius は、係数の反復 Frobenius と可換。 -/
theorem reesClosedRingThickeningFrobenius_scalar (n e : ℕ) (r : R) :
    reesClosedRingThickeningFrobenius I p hp hA n e
      (algebraMap R (A ⧸ (I ^ n).map (algebraMap R A)) r) =
    algebraMap R (A ⧸ (I ^ (p ^ e * n)).map (algebraMap R A))
      (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e) r) := by
  change reesClosedRingThickeningFrobenius I p hp hA n e
    (Ideal.Quotient.mk _ (algebraMap R A r)) =
    Ideal.Quotient.mk _ (algebraMap R A (frobeniusDirectSystemMap R p hp hR 0 e _ r))
  simp only [reesClosedRingThickeningFrobenius_mk, frobeniusDirectSystemMap_apply, Nat.sub_zero,
    map_pow]

/-- 実際の閉厚化の間の、反復 Frobenius に関する半線形写像。 -/
def reesClosedRingThickeningFrobeniusSemilinear (n e : ℕ) :
    (A ⧸ (I ^ n).map (algebraMap R A)) →ₛₗ[frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e)]
      (A ⧸ (I ^ (p ^ e * n)).map (algebraMap R A)) where
  toFun := reesClosedRingThickeningFrobenius I p hp hA n e
  map_add' := (reesClosedRingThickeningFrobenius I p hp hA n e).map_add
  map_smul' r x := by
    rw [Algebra.smul_def, map_mul,
      reesClosedRingThickeningFrobenius_scalar I p hp hR hA n e r, Algebra.smul_def]

/-- 半線形写像の値は、元の商環の写像そのもの。 -/
theorem reesClosedRingThickeningFrobeniusSemilinear_apply (n e : ℕ)
    (x : A ⧸ (I ^ n).map (algebraMap R A)) :
    reesClosedRingThickeningFrobeniusSemilinear I p hp hR hA n e x =
      reesClosedRingThickeningFrobenius I p hp hA n e x := rfl

end SerrePositivity.AlgebraicGeometry
