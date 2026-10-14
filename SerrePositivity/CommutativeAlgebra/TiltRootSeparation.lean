module

public import Mathlib.RingTheory.Perfectoid.Untilt
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Regular.Basic

/-! # pの根に対応するtilt元の分離性と正則性 -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable (S : Type*) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 元の環の互換根の列へ戻した第n成分。 -/
def tiltRootEvaluation (n : ℕ) : PreTilt S p →* S :=
  (Perfection.coeffMonoidHom S p n).comp
    (Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm.toMonoidHom

/-- この成分のmod p像は元のtilt座標。 -/
theorem tiltRootEvaluation_mod_p (n : ℕ) (x : PreTilt S p) :
    Ideal.Quotient.mk (Ideal.span {(p : S)}) (tiltRootEvaluation S p n x) =
      PreTilt.coeff n x := by
  have h := congrArg (Perfection.coeff (ModP S p) p n)
    ((Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).apply_symm_apply x)
  exact h

/-- 第n成分のp^n乗はuntilt。 -/
theorem tiltRootEvaluation_pow (n : ℕ) (x : PreTilt S p) :
    tiltRootEvaluation S p n x ^ p ^ n = x.untilt := by
  have h := Perfection.coeffMonoidHom_pow_p_pow_self
    ((Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm x) n
  exact h.trans (Perfection.coeff_zero_symm_quotientMulEquiv x)

/-- 零元の全ての持ち上げ成分は零。 -/
theorem tiltRootEvaluation_zero (n : ℕ) : tiltRootEvaluation S p n 0 = 0 := by
  let z : Perfection S p := ⟨fun _ ↦ 0, fun _ ↦ by simp [zero_pow (Fact.out : p.Prime).ne_zero]⟩
  have he : Perfection.quotientMulEquiv p (Ideal.span {(p : S)}) z = (0 : PreTilt S p) := by
    apply Perfection.ext
    intro i
    exact map_zero (Ideal.Quotient.mk (Ideal.span {(p : S)}))
  have hz := (Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm_apply_eq.mpr he.symm
  change Perfection.coeffMonoidHom S p n
    ((Perfection.quotientMulEquiv p (Ideal.span {(p : S)})).symm 0) = 0
  rw [hz]
  rfl

/-- pがuntilt(q)のp乗の単元倍なら、tiltはq進分離。 -/
theorem tilt_isHausdorff_of_unit_untilt_root (q : PreTilt S p) (u : Sˣ)
    (hp : (p : S) = u * q.untilt ^ p) :
    IsHausdorff (Ideal.span {q}) (PreTilt S p) := by
  constructor
  intro x hx
  have hdiv (m : ℕ) : ∃ y : PreTilt S p, q ^ m * y = x := by
    have h := SModEq.sub_mem.mp (hx m)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
    exact (Ideal.mem_span_singleton.mp (by simpa only [sub_zero] using h)).imp
      (fun _ he ↦ he.symm)
  have hz (n : ℕ) : tiltRootEvaluation S p n x = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {(p : S)})
    intro m
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    apply SModEq.sub_mem.mpr
    simp only [sub_zero]
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨y, hy⟩ := hdiv (p ^ (n + 1) * m)
    refine ⟨(↑(u⁻¹) : S) ^ m * tiltRootEvaluation S p n y, ?_⟩
    have hr : (p : S) = u * tiltRootEvaluation S p n q ^ p ^ (n + 1) := by
      rw [pow_succ, pow_mul, tiltRootEvaluation_pow]
      exact hp
    have hh := congrArg (tiltRootEvaluation S p n) hy
    rw [map_mul, map_pow] at hh
    rw [← hh, hr, mul_pow, pow_mul]
    have hu : (u : S) ^ m * (↑(u⁻¹) : S) ^ m = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((u : S) ^ m * (↑(u⁻¹) : S) ^ m) *
          (tiltRootEvaluation S p n q ^ (p ^ (n + 1) * m) *
            tiltRootEvaluation S p n y) := by rw [hu]; simp [pow_mul]
      _ = _ := by ring
  apply Perfection.ext
  intro n
  change PreTilt.coeff n x = 0
  rw [← tiltRootEvaluation_mod_p S p n x, hz, map_zero]

/-- untiltが正則ならtilt元自身も正則。 -/
theorem tilt_mul_injective_of_untilt_regular (q : PreTilt S p)
    (hq : Function.Injective (fun z : S ↦ q.untilt * z)) :
    Function.Injective (fun z : PreTilt S p ↦ q * z) := by
  apply (injective_iff_map_eq_zero (LinearMap.mulLeft (PreTilt S p) q)).mpr
  intro x hx
  change q * x = 0 at hx
  have hz (n : ℕ) : tiltRootEvaluation S p n x = 0 := by
    have hreg : IsLeftRegular (tiltRootEvaluation S p n q) :=
      (IsLeftRegular.pow_iff (pow_pos (Fact.out : p.Prime).pos n)).mp
        (by rw [tiltRootEvaluation_pow]; exact hq)
    apply hreg
    change tiltRootEvaluation S p n q * tiltRootEvaluation S p n x =
      tiltRootEvaluation S p n q * 0
    rw [mul_zero, ← map_mul, hx, tiltRootEvaluation_zero]
  apply Perfection.ext
  intro n
  change PreTilt.coeff n x = 0
  rw [← tiltRootEvaluation_mod_p S p n x, hz, map_zero]

end SerrePositivity
