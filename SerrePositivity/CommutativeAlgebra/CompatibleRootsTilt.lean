module

public import SerrePositivity.CommutativeAlgebra.PerfectionPrincipalKernel
public import SerrePositivity.CommutativeAlgebra.PrincipalQuotientAnnihilator
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.Algebra.Regular.Basic

/-! # 両立するp冪根によるtilt射影の核の判定

pの両立する根をmod pへ移し、実際のtiltの元を構成する。
pの正則性から商の零化元の条件を供給し、最初のFrobenius核だけから
全成分の割り算とtiltの第0射影の核を計算する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable (S : Type*) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))]

/-- 環内の両立する根の列をmod pへ移したtiltの元。 -/
def compatibleRootsTilt (ρ : ℕ → S) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) : PreTilt S p :=
  ⟨fun n ↦ Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ n),
    fun n ↦ by rw [← map_pow, hρ]⟩

@[simp] theorem compatibleRootsTilt_coeff (ρ : ℕ → S)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    PreTilt.coeff n (compatibleRootsTilt S p ρ hρ) =
      Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ n) := rfl

/-- 両立する根のtiltのuntiltは元の初項に一致する。 -/
theorem compatibleRootsTilt_untilt [IsAdicComplete (Ideal.span {(p : S)}) S]
    (ρ : ℕ → S) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    (compatibleRootsTilt S p ρ hρ).untilt = ρ 0 := by
  apply Perfection.teichmullerFun_spec
  intro n
  refine ⟨ρ n, rfl, ?_⟩
  have hh := compatibleRoots_pow p ρ hρ 0 n
  rw [Nat.zero_add] at hh
  rw [hh]

omit [Fact (¬ IsUnit (p : S))] in
/-- pの正則性は、その両立する各根の正則性を与える。 -/
theorem compatible_p_root_regular
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    Function.Injective (fun x : S ↦ ρ n * x) := by
  have hpow : ρ n ^ (p ^ n) = (p : S) := by
    simpa only [Nat.zero_add, hρ0] using compatibleRoots_pow p ρ hρ 0 n
  apply (IsLeftRegular.pow_iff (pow_pos (Fact.out : p.Prime).pos n)).mp
  change Function.Injective (fun x : S ↦ ρ n ^ (p ^ n) * x)
  simpa only [hpow] using hregular

omit [Fact (¬ IsUnit (p : S))] in
/-- 正の段のp冪根をmod pで零化する元は、Frobeniusで消える。 -/
theorem compatible_p_root_modP_annihilator
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (n : ℕ) (z : ModP S p)
    (hz : Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ (n + 1)) * z = 0) : z ^ p = 0 := by
  have hpow : ρ (n + 1) ^ (p ^ (n + 1)) = (p : S) := by
    simpa only [Nat.zero_add, hρ0] using compatibleRoots_pow p ρ hρ 0 (n + 1)
  have hpos : 0 < p ^ (n + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hge : p ≤ p ^ (n + 1) := by
    rw [pow_succ]
    have hh := pow_pos (Fact.out : p.Prime).pos n
    nlinarith
  have hbound : p ^ (n + 1) ≤ (p ^ (n + 1) - 1) * p := by
    have hp := (Fact.out : p.Prime).two_le
    have hh : p ^ (n + 1) - 1 + 1 = p ^ (n + 1) := Nat.sub_add_cancel hpos
    nlinarith
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hza : ρ (n + 1) * a ∈ Ideal.span {(p : S)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  have hnew : Ideal.Quotient.mk (Ideal.span {ρ (n + 1) ^ (p ^ (n + 1))}) (ρ (n + 1)) *
      Ideal.Quotient.mk _ a = 0 := by
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [hpow] using hza
  have hh := pow_eq_zero_of_mul_eq_zero_mod_regular_pow S (ρ (n + 1))
    (compatible_p_root_regular S p hregular ρ hρ0 hρ (n + 1)) _ p hpos hbound
    (Ideal.Quotient.mk _ a) hnew
  rw [← map_pow] at hh ⊢
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hh' := Ideal.Quotient.eq_zero_iff_mem.mp hh
  simpa only [hpow] using hh'

/-- pの両立する根について、最初のmod p Frobenius核からtilt射影の核を計算する。 -/
theorem compatibleRootsTilt_coeff_zero_kernel
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hker : ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) =
      Ideal.span {compatibleRootsTilt S p ρ hρ} := by
  change RingHom.ker (Perfection.coeff (ModP S p) p 0) = _
  refine perfection_coeff_zero_kernel_eq_span (ModP S p) p hF
    (compatibleRootsTilt S p ρ hρ) ?_ ?_ ?_
  · change Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 0) = 0
    rw [hρ0]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  · change ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}
    exact hker
  · intro n z hz
    exact compatible_p_root_modP_annihilator S p hregular ρ hρ0 hρ n z hz

end SerrePositivity
