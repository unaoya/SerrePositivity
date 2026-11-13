module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerMap
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimit

/-!
概要：局所化へ延長した反復 Frobenius は、実際の局所化環の p^e 乗である。
方針：局所化の分数公式と、局所化環の冪の公式を照合する。
規約：元の環と局所化の非自明性は仮定しない。
使われ方：厚化を経由する写像の因子分解を、既存の Frobenius 系へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
variable [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 反復 Frobenius を延長した局所化の写像は、実際の局所化環の冪写像。 -/
theorem projectiveLocalizedPowerMap_frobenius (s : P) (e : ℕ)
    (hd : frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e) (algebraMap P A s) =
      (algebraMap P A s) ^ (p ^ e))
    (hs : ∀ r, frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e)
        (algebraMap R A r) =
      algebraMap R A (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e) r))
    (z : LocalizedModule (Submonoid.powers s) A) :
    projectiveLocalizedPowerMap (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
      (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e)) s (p ^ e) hd hs z =
    z ^ (p ^ e) := by
  induction z using LocalizedModule.induction_on with
  | _ a t =>
    obtain ⟨t, n, rfl⟩ := t
    change projectiveLocalizedPowerMap _ _ s (p ^ e) hd hs
      (LocalizedModule.mk a (projDenominator s n)) =
      (LocalizedModule.mk a (projDenominator s n)) ^ (p ^ e)
    have hf : projectiveLocalizedPowerMap
        (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
        (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e)) s (p ^ e) hd hs
        (LocalizedModule.mk a (projDenominator s n)) =
        LocalizedModule.mk
          (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e) a)
          (projDenominator s (p ^ e * n)) := projectiveLocalizedPowerMap_fraction
      (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
      (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e)) s (p ^ e) hd hs a n
    rw [hf, LocalizedModule.mk_pow]
    simp only [frobeniusDirectSystemMap_apply, Nat.sub_zero]
    congr 1
    apply Subtype.ext
    change s ^ (p ^ e * n) = (s ^ n) ^ (p ^ e)
    simp only [pow_mul, Nat.mul_comm]

end SerrePositivity.AlgebraicGeometry
