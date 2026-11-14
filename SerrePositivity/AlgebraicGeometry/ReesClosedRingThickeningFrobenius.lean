module

public import SerrePositivity.AlgebraicGeometry.FrobeniusThickeningMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveRingQuotientGrading

/-!
概要：Rees の実際の商環表示 A/(Iⁿ A) の間に、厚化を経由する Frobenius を作る。
方針：代表元の p^e 乗で定義し、イデアルの拡大と冪の交換を使う。
規約：像の次数は p^e 倍になり、加群の I 進商と混同しない。
使われ方：閉厚化の標準開・Čech の Frobenius の因子分解。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

/-- Rees の環の商表示の、厚さ n から p^e*n への Frobenius。 -/
def reesClosedRingThickeningFrobenius (n e : ℕ) :
    A ⧸ (I ^ n).map (algebraMap R A) →+* A ⧸ (I ^ (p ^ e * n)).map (algebraMap R A) :=
  Ideal.Quotient.lift ((I ^ n).map (algebraMap R A))
    ((Ideal.Quotient.mk ((I ^ (p ^ e * n)).map (algebraMap R A))).comp
      (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e))) (by
    intro a ha
    rw [RingHom.comp_apply, frobeniusDirectSystemMap_apply, Nat.sub_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [Ideal.map_pow, ← pow_mul, Nat.mul_comm] using Ideal.pow_mem_pow ha (p ^ e))

/-- 実際の商環の厚化 Frobenius は代表元の p^e 乗。 -/
theorem reesClosedRingThickeningFrobenius_mk (n e : ℕ) (a : A) :
    reesClosedRingThickeningFrobenius I p hp hA n e
      (Ideal.Quotient.mk ((I ^ n).map (algebraMap R A)) a) =
    Ideal.Quotient.mk ((I ^ (p ^ e * n)).map (algebraMap R A)) (a ^ (p ^ e)) := by
  change Ideal.Quotient.mk _ (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e) a) = _
  rw [frobeniusDirectSystemMap_apply, Nat.sub_zero]

/-- 元の環から閉厚化への射影と、厚化を経由する反復 Frobenius の可換性。 -/
theorem reesClosedRingThickeningFrobenius_projection (n e : ℕ) :
    (reesClosedRingThickeningFrobenius I p hp hA n e).comp
      (Ideal.Quotient.mk ((I ^ n).map (algebraMap R A))) =
    (Ideal.Quotient.mk ((I ^ (p ^ e * n)).map (algebraMap R A))).comp
      (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e)) := rfl

/-- 厚化 Frobenius は、実際の商環の斉次次数を p^e 倍する。 -/
theorem reesClosedRingThickeningFrobenius_preservesPiece
    (G : ℕ → Submodule R A) [SetLike.GradedMonoid G] (n e k : ℕ)
    (x : A ⧸ (I ^ n).map (algebraMap R A))
    (hx : x ∈ projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G k) :
    reesClosedRingThickeningFrobenius I p hp hA n e x ∈
      projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G (p ^ e * k) := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a ^ (p ^ e), ?_, ?_⟩
  · change a ^ (p ^ e) ∈ G (p ^ e * k)
    simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded (p ^ e) ha
  · exact (reesClosedRingThickeningFrobenius_mk I p hp hA n e a).symm

end SerrePositivity.AlgebraicGeometry
