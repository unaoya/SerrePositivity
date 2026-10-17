module

public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealRadical
public import SerrePositivity.BhattScholze.CompatibleRootCompletionPerfectoid

/-! # The original perfectoid ideal and the ideal of compatible roots modulo p powers

The chosen B3 quotient is compared to the actual completed compatible-root quotient
through their original universal maps. No general integral perfectoidization input is used.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open BhattScholze
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
include hρ

/-- The actual B3 kernel is the kernel of the actual completed root-ideal quotient map. -/
theorem perfectoidIdeal_eq_compatibleRootCompletion_kernel :
    perfectoidIdeal R p hR (ρ 0) = RingHom.ker
      ((algebraMap (R ⧸ SerrePositivity.compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)).comp
        (Ideal.Quotient.mk (SerrePositivity.compatibleRootIdeal ρ))) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {ρ 0}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton (ρ 0))
  have hf := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {ρ 0}) p hR
  have hg := compatibleRootCompletionMap_isPerfectoidization hR ρ hρ
  have he := IsPerfectoidization.ker_comp_eq p hf hg (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  have hc : (compatibleRootCompletionMap p ρ).comp (Ideal.Quotient.mk (Ideal.span {ρ 0})) =
      (algebraMap (R ⧸ SerrePositivity.compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)).comp
        (Ideal.Quotient.mk (SerrePositivity.compatibleRootIdeal ρ)) := by
    ext x
    rfl
  rw [hc] at he
  exact he

/-- At every p-power precision, elements of the perfectoid ideal lie in the root ideal. -/
theorem perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow (k : ℕ) :
    perfectoidIdeal R p hR (ρ 0) ≤ SerrePositivity.compatibleRootIdeal ρ ⊔
      Ideal.span {(p : R) ^ k} := by
  let J := SerrePositivity.compatibleRootIdeal ρ
  let Q := R ⧸ J
  let q : R →+* Q := Ideal.Quotient.mk J
  let P : Ideal Q := Ideal.span {(p : Q)}
  let K : Ideal R := Ideal.span {(p : R) ^ k}
  intro x hx
  rw [perfectoidIdeal_eq_compatibleRootCompletion_kernel R p hR ρ hρ] at hx
  change algebraMap Q (CompatibleRootCompletion p ρ) (q x) = 0 at hx
  have hy := congrArg (AdicCompletion.evalₐ P k) hx
  simp only [AdicCompletion.algebraMap_apply, map_zero] at hy
  have hmem : q x ∈ P ^ k := Ideal.Quotient.eq_zero_iff_mem.mp hy
  have hmap : K.map q = P ^ k := by
    simp only [K, P, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
      Ideal.span_singleton_pow]
  have hxmap : x ∈ (K.map q).comap q := by
    change q x ∈ K.map q
    rw [hmap]
    exact hmem
  have hcomap : (K.map q).comap q = K ⊔ J := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hcomap] at hxmap
  exact (sup_comm K J ▸ hxmap)

/-- The roots themselves lie in the original B3 perfectoid ideal. -/
theorem compatibleRootIdeal_le_perfectoidIdeal :
    SerrePositivity.compatibleRootIdeal ρ ≤ perfectoidIdeal R p hR (ρ 0) := by
  rw [perfectoidIdeal_eq_compatibleRootCompletion_kernel R p hR ρ hρ]
  intro x hx
  change algebraMap (R ⧸ SerrePositivity.compatibleRootIdeal ρ)
    (CompatibleRootCompletion p ρ) (Ideal.Quotient.mk _ x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- The ideal and the explicit root ideal agree to every p-power precision. -/
theorem perfectoidIdeal_sup_p_pow_eq_compatibleRootIdeal (k : ℕ) :
    perfectoidIdeal R p hR (ρ 0) ⊔ Ideal.span {(p : R) ^ k} =
      SerrePositivity.compatibleRootIdeal ρ ⊔ Ideal.span {(p : R) ^ k} := by
  apply le_antisymm
  · exact sup_le (perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow R p hR ρ hρ k) le_sup_right
  · exact sup_le_sup (compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ) le_rfl

/-- The images in the actual R/p^k quotient agree, including k = 0. -/
theorem perfectoidIdeal_mod_p_pow_eq_compatibleRootIdeal (k : ℕ) :
    (perfectoidIdeal R p hR (ρ 0)).map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) =
      (SerrePositivity.compatibleRootIdeal ρ).map
        (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) := by
  apply (Ideal.map_eq_iff_sup_ker_eq_of_surjective
    (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) Ideal.Quotient.mk_surjective).mpr
  rw [Ideal.mk_ker]
  exact perfectoidIdeal_sup_p_pow_eq_compatibleRootIdeal R p hR ρ hρ k

/-- Any ideal containing p^k contains the perfectoid ideal exactly when it contains every root. -/
theorem perfectoidIdeal_le_iff_compatible_roots (J : Ideal R) (k : ℕ)
    (hp : (p : R) ^ k ∈ J) :
    perfectoidIdeal R p hR (ρ 0) ≤ J ↔ ∀ n, ρ n ∈ J := by
  constructor
  · intro h n
    exact h ((compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ)
      (Ideal.mem_span_range_self (x := n)))
  · intro h
    apply (perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow R p hR ρ hρ k).trans
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact h n
    · exact (Ideal.span_singleton_le_iff_mem J).mpr hp

/-- A p-adically separated ideal quotient detects containment of the perfectoid
ideal through the original compatible roots. -/
theorem perfectoidIdeal_le_iff_compatible_roots_of_quotient_isHausdorff
    (J : Ideal R) [IsHausdorff (Ideal.span {(p : R ⧸ J)}) (R ⧸ J)] :
    perfectoidIdeal R p hR (ρ 0) ≤ J ↔ ∀ n, ρ n ∈ J := by
  constructor
  · intro h n
    exact h ((compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ)
      (Ideal.mem_span_range_self (x := n)))
  · intro h s hs
    let Q := R ⧸ J
    let q : R →+* Q := Ideal.Quotient.mk J
    have hroot : SerrePositivity.compatibleRootIdeal ρ ≤ J := by
      apply Ideal.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact h n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsHausdorff.haus
      (inferInstance : IsHausdorff (Ideal.span {(p : Q)}) Q) (q s)
    intro k
    obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp
      (perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow R p hR ρ hρ k hs)
    have hqy : q y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hroot hy)
    have hqz : q z ∈ (Ideal.span {(p : Q)}) ^ k := by
      have hm := Ideal.mem_map_of_mem q hz
      simpa only [Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
        Ideal.span_singleton_pow] using hm
    have he : q s = q z := by rw [← hsum, map_add, hqy, zero_add]
    apply SModEq.zero.mpr
    change q s ∈ (Ideal.span {(p : Q)}) ^ k • (⊤ : Ideal Q)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, he]
    exact hqz

/-- On an arbitrary p-power torsion module, almost zero is detected by
the action of each compatible root. -/
theorem perfectoidIdeal_annihilates_iff_compatible_roots
    (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (hM : ∀ x : M, (p : R) ^ k • x = 0) :
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0), ∀ x : M, s • x = 0) ↔
      ∀ n, ∀ x : M, ρ n • x = 0 := by
  constructor
  · intro h n x
    exact h _ ((compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ)
      (Ideal.mem_span_range_self (x := n))) x
  · intro h s hs x
    have hroots : ∀ n, ρ n ∈ Module.annihilator R M :=
      fun n => Module.mem_annihilator.mpr (h n)
    have hI := (perfectoidIdeal_le_iff_compatible_roots R p hR ρ hρ
      (Module.annihilator R M) k (Module.mem_annihilator.mpr hM)).mpr hroots
    exact Module.mem_annihilator.mp (hI hs) x

end SerrePositivity
