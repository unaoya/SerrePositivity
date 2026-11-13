module

public import SerrePositivity.AlgebraicGeometry.ReesClosedRingThickeningSemilinear
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerMap

/-!
概要：実際の閉厚化の反復 Frobenius を標準開の加群局所化へ移す。
方針：係数環の元の像を p^e 乗に送ることから局所化の半線形写像を作る。
規約：分母の指数は p^e 倍、厚さも p^e 倍。
使われ方：指定次数の係数図式と Čech H の因子分解。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
variable [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

omit [Algebra R P] [IsScalarTower R P A] in
/-- 厚化 Frobenius は、任意の係数環の元の像を p^e 乗に送る。 -/
theorem reesClosedRingThickeningFrobenius_algebraMap (n e : ℕ) (s : P) :
    reesClosedRingThickeningFrobenius I p hp hA n e
      (algebraMap P (A ⧸ (I ^ n).map (algebraMap R A)) s) =
    (algebraMap P (A ⧸ (I ^ (p ^ e * n)).map (algebraMap R A)) s) ^ (p ^ e) := by
  change reesClosedRingThickeningFrobenius I p hp hA n e
    (Ideal.Quotient.mk _ (algebraMap P A s)) =
    (Ideal.Quotient.mk _ (algebraMap P A s)) ^ (p ^ e)
  rw [reesClosedRingThickeningFrobenius_mk, map_pow]

/-- 実際の閉厚化の標準開の局所化の間の反復 Frobenius。 -/
def reesClosedLocalizedThickeningFrobenius (s : P) (n e : ℕ) :
    LocalizedModule (Submonoid.powers s) (A ⧸ (I ^ n).map (algebraMap R A))
      →ₛₗ[frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e)]
    LocalizedModule (Submonoid.powers s) (A ⧸ (I ^ (p ^ e * n)).map (algebraMap R A)) :=
  projectiveLocalizedPowerMap (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
    (reesClosedRingThickeningFrobenius I p hp hA n e) s (p ^ e)
    (reesClosedRingThickeningFrobenius_algebraMap I p hp hA n e s)
    (reesClosedRingThickeningFrobenius_scalar I p hp hR hA n e)

/-- 厚化 Frobenius は分子を p^e 乗、分母の指数を p^e 倍に送る。 -/
theorem reesClosedLocalizedThickeningFrobenius_fraction (s : P) (n e m : ℕ) (a : A) :
    reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e
      (LocalizedModule.mk (Ideal.Quotient.mk ((I ^ n).map (algebraMap R A)) a)
        (⟨s ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers s)) =
    LocalizedModule.mk
      (Ideal.Quotient.mk ((I ^ (p ^ e * n)).map (algebraMap R A)) (a ^ (p ^ e)))
      (⟨s ^ (p ^ e * m), ⟨p ^ e * m, rfl⟩⟩ : Submonoid.powers s) := by
  rw [reesClosedLocalizedThickeningFrobenius, projectiveLocalizedPowerMap_fraction,
    reesClosedRingThickeningFrobenius_mk]

end SerrePositivity.AlgebraicGeometry
