module

public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusCriterion
public import SerrePositivity.CommutativeAlgebra.FrobeniusRootKernels

/-! # 特別な Fontaine 核の生成元から Frobenius 核を計算する

核が p+[q]^p c で生成される場合、第零 Witt 係数と tilt の完全性だけで
x^p∈(π^p) から x∈(π) を導く。導来圏や追加の被約性は要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open PerfectoidFrobeniusCriterion

theorem fontaine_frobenius_kernel_of_primitive_generator
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hθ : Function.Surjective (WittVector.fontaineTheta S p))
    (π : S) (q : PreTilt S p) (v : Sˣ) (hq : q.untilt = v * π)
    (c : WittVector p (PreTilt S p))
    (hker : RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * c})
    (x : S) (hx : x ^ p ∈ Ideal.span {π ^ p}) : x ∈ Ideal.span {π} := by
  let θ := WittVector.fontaineTheta S p
  let tq := WittVector.teichmuller p q
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨w, hw⟩ := hθ x
  obtain ⟨z, hz⟩ := hθ ((↑(v⁻¹) : S) ^ p * b)
  have hdiff : w ^ p - tq ^ p * z ∈ RingHom.ker θ := by
    change θ (w ^ p - tq ^ p * z) = 0
    rw [map_sub, map_pow, hw, map_mul, map_pow]
    rw [show θ tq = q.untilt from WittVector.fontaineTheta_teichmuller q]
    rw [hz, hq, mul_pow, hb]
    have hv : (v : S) ^ p * (↑(v⁻¹) : S) ^ p = 1 := by rw [← mul_pow]; simp
    calc
      _ = π ^ p * b * (1 - (v : S) ^ p * (↑(v⁻¹) : S) ^ p) := by ring
      _ = 0 := by rw [hv, sub_self, mul_zero]
  rw [hker] at hdiff
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hdiff
  have hcoeff := congrArg (WittVector.constantCoeff : WittVector p (PreTilt S p) →+*
    PreTilt S p) ha
  have hcoeff' : w.coeff 0 ^ p - q ^ p * z.coeff 0 = q ^ p * c.coeff 0 * a.coeff 0 := by
    simpa only [map_sub, map_pow, map_mul, map_add, WittVector.constantCoeff_apply, tq,
      WittVector.coeff_p_zero, zero_add, WittVector.teichmuller_coeff_zero] using hcoeff
  have hwPow : w.coeff 0 ^ p ∈ Ideal.span {q ^ p} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z.coeff 0 + c.coeff 0 * a.coeff 0, ?_⟩
    linear_combination hcoeff'
  have hwq : w.coeff 0 ∈ Ideal.span {q} := by
    let e := perfectFrobeniusQuotientEquiv (PreTilt S p) p q
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [map_zero, perfectFrobeniusQuotientEquiv_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hwPow
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hwq
  have hres : w - tq * WittVector.teichmuller p r ∈
      Ideal.span {(p : WittVector p (PreTilt S p))} := by
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change (WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _)
      (w - tq * WittVector.teichmuller p r) = 0
    simpa only [map_sub, map_mul, WittVector.constantCoeff_apply, tq,
      WittVector.teichmuller_coeff_zero] using sub_eq_zero.mpr hr
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hres
  have heq := congrArg θ hd
  have hqI : q.untilt ∈ Ideal.span {π} := by
    rw [hq]
    exact (Ideal.span {π}).mul_mem_left (v : S) (Ideal.subset_span (Set.mem_singleton _))
  have hpdiv : (p : S) ∈ Ideal.span {π} := by
    have hβ : (p : WittVector p (PreTilt S p)) + tq ^ p * c ∈ RingHom.ker θ := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton _)
    change θ ((p : WittVector p (PreTilt S p)) + tq ^ p * c) = 0 at hβ
    have hβ' : (p : S) + q.untilt ^ p * θ c = 0 := by
      simpa only [map_add, map_natCast, map_mul, map_pow, θ, tq,
        WittVector.fontaineTheta_teichmuller] using hβ
    have hm : q.untilt ^ p * θ c ∈ Ideal.span {π} :=
      (Ideal.span {π}).mul_mem_right _
        (Ideal.pow_mem_of_mem _ hqI p (Fact.out : p.Prime).pos)
    have hpEq : (p : S) = -(q.untilt ^ p * θ c) := eq_neg_of_add_eq_zero_left hβ'
    rw [hpEq]
    exact (Ideal.span {π}).neg_mem hm
  have heq' : x - q.untilt * r.untilt = (p : S) * θ d := by
    simpa only [map_sub, map_mul, map_natCast, θ, tq, hw,
      WittVector.fontaineTheta_teichmuller] using heq
  have hxEq : x = q.untilt * r.untilt + (p : S) * θ d := by linear_combination heq'
  rw [hxEq]
  exact (Ideal.span {π}).add_mem
    ((Ideal.span {π}).mul_mem_right _ hqI)
    ((Ideal.span {π}).mul_mem_right _ hpdiv)

/-- 整perfectoidの四条件から、単元倍のp乗根に対するFrobenius核条件を供給する。
πの正則性や環の被約性を追加の前提にしない。 -/
theorem IsIntegralPerfectoid.frobenius_kernel_of_unit_root
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p)
    (x : S) (hx : x ^ p ∈ Ideal.span {π ^ p}) : x ∈ Ideal.span {π} := by
  rcases hS with hsub | ⟨hp, hc, _, hF, hker⟩
  · rw [Subsingleton.elim x 0]
    exact Ideal.zero_mem _
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    obtain ⟨q, v, c, hq, hgen⟩ :=
      exists_untilt_unit_mul_and_kernel_generator S p hF hker π u hpEq
    exact fontaine_frobenius_kernel_of_primitive_generator S p
      (surjective_fontaineTheta hF) π q v hq c hgen x hx

/-- compatibleなp冪根の系について、四条件から全反復Frobeniusの核を計算する。
非零のmod p商を扱うためpの非可逆性を明示し、零環の処理は別の入口へ分離する。 -/
theorem IsIntegralPerfectoid.pow_kernel_of_compatible_roots
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : S))]
    (hS : IsIntegralPerfectoid S p) (ρ : ℕ → S) (hρ₀ : ρ 0 = (p : S))
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) (x : S) :
    x ^ (p ^ n) ∈ Ideal.span {(p : S)} ↔ x ∈ Ideal.span {ρ n} := by
  have hnonzero : ¬ Subsingleton S := by
    intro hsub
    let : Subsingleton S := hsub
    apply (Fact.out : ¬ IsUnit (p : S))
    rw [Subsingleton.elim (p : S) 1]
    exact isUnit_one
  obtain ⟨_, _, _, hF, _⟩ := hS.resolve_left hnonzero
  let f := Ideal.Quotient.mk (Ideal.span {(p : S)})
  let e : ℕ → ModP S p := fun m ↦ f (ρ m)
  have he0 : e 0 = 0 := by
    dsimp only [e]
    rw [hρ₀]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have he (m : ℕ) : e (m + 1) ^ p = e m := by
    dsimp only [e]
    rw [← map_pow, hρ m]
  have hρ₁ : ρ 1 ^ p = (p : S) := (hρ 0).trans hρ₀
  have hfirst (y : ModP S p) : y ^ p = 0 ↔ y ∈ Ideal.span {e 1} := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · intro hz
      have hzmem : z ^ p ∈ Ideal.span {(p : S)} := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa only [map_pow] using hz
      have hzroot : z ∈ Ideal.span {ρ 1} :=
        hS.frobenius_kernel_of_unit_root S p (ρ 1) 1 (by simpa using hρ₁.symm) z
          (by simpa only [hρ₁] using hzmem)
      have hm := Ideal.mem_map_of_mem f hzroot
      simpa only [Ideal.map_span, Set.image_singleton] using hm
    · intro hz
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
      rw [ha, mul_pow, show (f (ρ 1)) ^ p = 0 from by
        rw [← map_pow, hρ₁]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)),
        zero_mul]
  have heq := frobenius_pow_kernel_iff_mem_span (ModP S p) p hF e he0 he hfirst n (f x)
  have hpre : f x ∈ Ideal.span {e n} ↔ x ∈ Ideal.span {ρ n} := by
    rw [show Ideal.span {e n} = (Ideal.span {ρ n}).map f from by
      rw [Ideal.map_span, Set.image_singleton]]
    change x ∈ Ideal.comap f ((Ideal.span {ρ n}).map f) ↔ _
    rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective]
    change x ∈ Ideal.span {ρ n} ⊔ RingHom.ker
      (Ideal.Quotient.mk (Ideal.span {(p : S)})) ↔ _
    rw [Ideal.mk_ker]
    have hpMem : (p : S) ∈ Ideal.span {ρ n} := by
      have hpEq : ρ n ^ (p ^ n) = (p : S) := by
        simpa only [zero_add, hρ₀] using compatibleRoots_pow p ρ hρ 0 n
      rw [← hpEq]
      exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _
        (pow_pos (Fact.out : p.Prime).pos _)
    rw [sup_eq_left.mpr ((Ideal.span {ρ n}).span_singleton_le_iff_mem.mpr hpMem)]
  rw [← map_pow, hpre] at heq
  change (Ideal.Quotient.mk (Ideal.span {(p : S)}) (x ^ (p ^ n)) = 0 ↔
    x ∈ Ideal.span {ρ n}) at heq
  simpa only [Ideal.Quotient.eq_zero_iff_mem] using heq

end SerrePositivity
