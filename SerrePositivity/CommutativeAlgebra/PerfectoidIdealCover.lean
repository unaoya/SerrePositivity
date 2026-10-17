module

public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealCompatibleRoots
public import SerrePositivity.BhattScholze.CompatibleRootFamilyCompletionPerfectoid

/-! # Gluing perfectoid-ideal annihilation from a rooted cover

A power of the original generator in the cover ideal suffices. The root-family
completion detects the original ideal, and evaluation at p-power precision
returns to the ordinary sum of the local perfectoid ideals.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open BhattScholze
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- Any map to a perfectoid ring killing g kills the original perfectoid ideal. -/
theorem perfectoidIdeal_le_ker_of_eq_zero {T : Type u} [CommRing T]
    (hT : IsIntegralPerfectoid T p) (f : R →+* T) (g : R) (hg : f g = 0) :
    perfectoidIdeal R p hR g ≤ RingHom.ker f := by
  let k : R ⧸ Ideal.span {g} →+* T := Ideal.Quotient.lift _ f
    (fun a ha => ((Ideal.span_singleton_le_iff_mem (RingHom.ker f)).mpr hg) ha)
  obtain ⟨l, hl, _⟩ :=
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).2 T hT k
  intro x hx
  change toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk _ x) = 0 at hx
  have he := RingHom.congr_fun hl (Ideal.Quotient.mk (Ideal.span {g}) x)
  change l (toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk _ x)) = f x at he
  rw [hx, map_zero] at he
  exact he.symm

/-- A rooted cover controls the original ideal to every p-power precision. -/
theorem perfectoidIdeal_le_compatibleRootFamilyIdeal_sup_p_pow
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (N : ℕ) (hcover : g ^ N ∈ compatibleRootFamilyZeroIdeal ρ) (k : ℕ) :
    perfectoidIdeal R p hR g ≤ compatibleRootFamilyIdeal ρ ⊔ Ideal.span {(p : R) ^ k} := by
  let J := compatibleRootFamilyIdeal ρ
  let Q := R ⧸ J
  let q : R →+* Q := Ideal.Quotient.mk J
  let P := CompatibleRootFamilyCompletion p ρ
  let κ : R →+* P := (algebraMap Q P).comp q
  have hP : IsIntegralPerfectoid P p := compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ
  let := hP.isReduced P p
  have hg : κ g = 0 := by
    apply IsReduced.eq_zero
    refine ⟨N, ?_⟩
    rw [← map_pow]
    change algebraMap Q P (q (g ^ N)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (compatibleRootFamilyZeroIdeal_le ρ hcover), map_zero]
  have hI := perfectoidIdeal_le_ker_of_eq_zero R p hR hP κ g hg
  intro x hx
  have hz := hI hx
  change algebraMap Q P (q x) = 0 at hz
  have hy := congrArg (AdicCompletion.evalₐ (Ideal.span {(p : Q)}) k) hz
  simp only [map_zero] at hy
  have hmem : q x ∈ (Ideal.span {(p : Q)}) ^ k := Ideal.Quotient.eq_zero_iff_mem.mp hy
  let K : Ideal R := Ideal.span {(p : R) ^ k}
  have hmap : K.map q = (Ideal.span {(p : Q)}) ^ k := by
    simp only [K, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
      Ideal.span_singleton_pow]
  have hxmap : x ∈ (K.map q).comap q := by
    change q x ∈ K.map q
    rw [hmap]
    exact hmem
  have hcomap : (K.map q).comap q = K ⊔ J := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hcomap] at hxmap
  exact sup_comm K J ▸ hxmap

/-- The local perfectoid ideals generate the original one modulo each p power. -/
theorem perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (N : ℕ) (hcover : g ^ N ∈ compatibleRootFamilyZeroIdeal ρ) (k : ℕ) :
    perfectoidIdeal R p hR g ≤ (⨆ s, perfectoidIdeal R p hR (ρ s 0)) ⊔
      Ideal.span {(p : R) ^ k} := by
  apply (perfectoidIdeal_le_compatibleRootFamilyIdeal_sup_p_pow R p hR ρ hρ g N hcover k).trans
  apply sup_le_sup _ le_rfl
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  exact (le_iSup (fun s => perfectoidIdeal R p hR (ρ s 0)) s)
    ((compatibleRootIdeal_le_perfectoidIdeal R p hR (ρ s) (hρ s))
      (Ideal.mem_span_range_self (x := n)))

/-- Local almost annihilation glues on arbitrary p-power-torsion modules.
The cover need not be finite and the test module need not be finitely generated. -/
theorem perfectoidIdeal_annihilates_of_rooted_cover
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (N : ℕ) (hcover : g ^ N ∈ compatibleRootFamilyZeroIdeal ρ)
    (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (hM : ∀ x : M, (p : R) ^ k • x = 0)
    (hlocal : ∀ s, ∀ a ∈ perfectoidIdeal R p hR (ρ s 0), ∀ x : M, a • x = 0) :
    ∀ a ∈ perfectoidIdeal R p hR g, ∀ x : M, a • x = 0 := by
  have hsum : (⨆ s, perfectoidIdeal R p hR (ρ s 0)) ≤ Module.annihilator R M :=
    iSup_le (fun s a ha => Module.mem_annihilator.mpr (hlocal s a ha))
  have hp : Ideal.span {(p : R) ^ k} ≤ Module.annihilator R M :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Module.mem_annihilator.mpr hM)
  have hI := (perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover R p hR ρ hρ g N hcover k).trans
    (sup_le hsum hp)
  exact fun a ha => Module.mem_annihilator.mp (hI ha)

end SerrePositivity
