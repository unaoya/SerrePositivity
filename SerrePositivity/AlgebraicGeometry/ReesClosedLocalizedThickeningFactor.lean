module

public import SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningNaturality

/-!
概要：厚化を経由する局所化の Frobenius の因子分解と射影の比較。
方針：商の代表元と分数を取り、分子・分母の p^e 乗を照合する。
規約：写像は実際の商環の線形局所化、右辺は局所化環の冪。
使われ方：十分厚い段への単射性と像の安定化を Frobenius に適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

private theorem thickeningFraction (s : MvPolynomial ι R) (n e j : ℕ) (a : A) :
    reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e
      (LocalizedModule.mk (Ideal.Quotient.mk ((I ^ n).map (algebraMap R A)) a)
        (projDenominator s j)) =
    LocalizedModule.mk
      (Ideal.Quotient.mk ((I ^ (p ^ e * n)).map (algebraMap R A)) (a ^ (p ^ e)))
      (projDenominator s (p ^ e * j)) :=
  reesClosedLocalizedThickeningFrobenius_fraction I p hp hR hA s n e j a

/-- 厚化を経由して元の厚さへ戻すと、実際の局所化環の p^e 乗になる。 -/
theorem reesClosedLocalizedThickeningFrobenius_factor
    (s : MvPolynomial ι R) (n e : ℕ)
    (z : LocalizedModule (Submonoid.powers s) (A ⧸ (I ^ n).map (algebraMap R A))) :
    IsLocalizedModule.map (Submonoid.powers s)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
      (reesClosedRingTransition (ι := ι) I (p ^ e * n) n
        (Nat.le_mul_of_pos_left n (pow_pos hp.pos e))).toLinearMap
      (reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e z) =
    z ^ (p ^ e) := by
  induction z using LocalizedModule.induction_on with
  | _ a t =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t, j, rfl⟩ := t
    change IsLocalizedModule.map (Submonoid.powers s) _ _ _
      (reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e
        (LocalizedModule.mk (Ideal.Quotient.mk _ a) (projDenominator s j))) =
      (LocalizedModule.mk (Ideal.Quotient.mk _ a) (projDenominator s j)) ^ (p ^ e)
    rw [thickeningFraction, IsLocalizedModule.map_LocalizedModules]
    change LocalizedModule.mk (Ideal.Quotient.mk _ (a ^ (p ^ e)))
      (projDenominator s (p ^ e * j)) = _
    rw [LocalizedModule.mk_pow, ← map_pow]
    congr 1
    apply Subtype.ext
    change s ^ (p ^ e * j) = (s ^ j) ^ (p ^ e)
    simp only [pow_mul, Nat.mul_comm]

/-- 商への射影と厚化 Frobenius の合成は、元の局所化の p^e 乗の射影。 -/
theorem reesClosedLocalizedThickeningFrobenius_projection
    (s : MvPolynomial ι R) (n e : ℕ) (z : LocalizedModule (Submonoid.powers s) A) :
    reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e
      (IsLocalizedModule.map (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) A)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
        (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A))).toLinearMap z) =
    IsLocalizedModule.map (Submonoid.powers s)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) A)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
      (Ideal.Quotient.mkₐ (MvPolynomial ι R)
        ((I ^ (p ^ e * n)).map (algebraMap R A))).toLinearMap (z ^ (p ^ e)) := by
  induction z using LocalizedModule.induction_on with
  | _ a t =>
    obtain ⟨t, j, rfl⟩ := t
    change reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e
      (IsLocalizedModule.map (Submonoid.powers s) _ _ _
        (LocalizedModule.mk a (projDenominator s j))) =
      IsLocalizedModule.map (Submonoid.powers s) _ _ _
        ((LocalizedModule.mk a (projDenominator s j)) ^ (p ^ e))
    rw [IsLocalizedModule.map_LocalizedModules, LocalizedModule.mk_pow,
      IsLocalizedModule.map_LocalizedModules]
    change reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e
      (LocalizedModule.mk (Ideal.Quotient.mk _ a) (projDenominator s j)) = _
    rw [thickeningFraction]
    congr 1
    apply Subtype.ext
    change s ^ (p ^ e * j) = (s ^ j) ^ (p ^ e)
    simp only [pow_mul, Nat.mul_comm]

end SerrePositivity.AlgebraicGeometry
