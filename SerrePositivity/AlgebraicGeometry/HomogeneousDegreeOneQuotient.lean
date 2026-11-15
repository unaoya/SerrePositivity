module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneSpecialization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：次数一の元を 1 とする商と、対応する斉次局所化の同型。
方針：正規化を商へ降ろし、商写像による特殊化を逆写像にする。
規約：分母の非零性・平坦性・次数一生成を仮定しない。
使われ方：Segre の標準開のテンソル積との比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)

/-- 脱斉次化の商から斉次局所化への実際の環写像。 -/
def homogeneousDegreeOneQuotientToAway :
    (A ⧸ Ideal.span ({f - 1} : Set A)) →+* HomogeneousLocalization.Away G f :=
  Ideal.Quotient.lift _ (homogeneousDegreeOneNormalize G hf) (by
    have hle : Ideal.span ({f - 1} : Set A) ≤ RingHom.ker (homogeneousDegreeOneNormalize G hf) := by
      apply Ideal.span_le.mpr
      rintro x (rfl : x = f - 1)
      change homogeneousDegreeOneNormalize G hf (f - 1) = 0
      rw [map_sub, map_one, homogeneousDegreeOneNormalize_self, sub_self]
    exact fun x hx ↦ hle hx)

/-- 商では、次数一の分母は 1 に等しい。 -/
theorem homogeneousDegreeOneQuotient_denominator :
    Ideal.Quotient.mk (Ideal.span ({f - 1} : Set A)) f = 1 :=
  (Ideal.Quotient.mk_eq_one_iff_sub_mem f).mpr (Ideal.subset_span (Set.mem_singleton _))

/-- 斉次局所化から脱斉次化の商への実際の特殊化。 -/
def homogeneousDegreeOneAwayToQuotient :
    HomogeneousLocalization.Away G f →+* (A ⧸ Ideal.span ({f - 1} : Set A)) :=
  homogeneousDegreeOneSpecialize G (Ideal.Quotient.mk _) (homogeneousDegreeOneQuotient_denominator (f := f))

/-- 次数一の元を 1 とする商は、対応する斉次局所化と同型。 -/
def homogeneousDegreeOneQuotientEquiv :
    (A ⧸ Ideal.span ({f - 1} : Set A)) ≃+* HomogeneousLocalization.Away G f where
  __ := homogeneousDegreeOneQuotientToAway G hf
  invFun := homogeneousDegreeOneAwayToQuotient G
  left_inv z := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change homogeneousDegreeOneSpecialize G (Ideal.Quotient.mk _)
      (homogeneousDegreeOneQuotient_denominator (f := f))
      (homogeneousDegreeOneNormalize G hf x) = Ideal.Quotient.mk _ x
    exact homogeneousDegreeOneSpecialize_normalize G hf _ _ x
  right_inv z := by
    obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective G hf z
    change homogeneousDegreeOneQuotientToAway G hf
      (homogeneousDegreeOneSpecialize G (Ideal.Quotient.mk _)
        (homogeneousDegreeOneQuotient_denominator (f := f))
        (HomogeneousLocalization.Away.mk G hf n x hx)) = _
    rw [homogeneousDegreeOneSpecialize_mk G hf]
    change homogeneousDegreeOneNormalize G hf x = _
    exact homogeneousDegreeOneNormalize_of_mem G hf x (by simpa using hx)

/-- 商の元における同型の式。 -/
theorem homogeneousDegreeOneQuotientEquiv_mk (x : A) :
    homogeneousDegreeOneQuotientEquiv G hf (Ideal.Quotient.mk _ x) =
      homogeneousDegreeOneNormalize G hf x := rfl

end SerrePositivity.AlgebraicGeometry
