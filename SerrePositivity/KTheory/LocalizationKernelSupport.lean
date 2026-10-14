module
public import SerrePositivity.KTheory.G0Localization

/-! # A localization kernel element comes from one smaller closed support -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

lemma supportZeroLocus_mul_left (s t : R) :
    supportZeroLocus (Ideal.span ({s} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s * t} : Set R)) := by
  intro p hp
  change Ideal.span ({s * t} : Set R) ≤ p.asIdeal
  apply Ideal.span_le.mpr
  intro a ha
  have ha' : a = s * t := Set.mem_singleton_iff.mp ha
  subst a
  exact p.asIdeal.mul_mem_right t (hp (Ideal.subset_span (Set.mem_singleton s)))

lemma supportZeroLocus_mul_right (s t : R) :
    supportZeroLocus (Ideal.span ({t} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s * t} : Set R)) := by
  simpa only [mul_comm] using supportZeroLocus_mul_left t s

variable (P : Submonoid R) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
/-- An element can be represented on the vanishing locus of one denominator. -/
def HasPrincipalLocalizationSupport (x : G0WithSupport Z) : Prop :=
  ∃ s ∈ P, ∃ y : G0WithSupport (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
    G0WithSupport.enlarge inf_le_left y = x

namespace HasPrincipalLocalizationSupport
variable {P Z}
lemma zero : HasPrincipalLocalizationSupport P Z 0 :=
  ⟨1, P.one_mem, 0, map_zero _⟩

lemma neg {x : G0WithSupport Z} (hx : HasPrincipalLocalizationSupport P Z x) :
    HasPrincipalLocalizationSupport P Z (-x) := by
  obtain ⟨s, hs, y, hy⟩ := hx
  exact ⟨s, hs, -y, by rw [map_neg, hy]⟩

lemma add {x x' : G0WithSupport Z} (hx : HasPrincipalLocalizationSupport P Z x)
    (hx' : HasPrincipalLocalizationSupport P Z x') :
    HasPrincipalLocalizationSupport P Z (x + x') := by
  obtain ⟨s, hs, y, hy⟩ := hx
  obtain ⟨t, ht, y', hy'⟩ := hx'
  let h₁ : Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤
      Z ⊓ supportZeroLocus (Ideal.span ({s * t} : Set R)) :=
    inf_le_inf_left Z (supportZeroLocus_mul_left s t)
  let h₂ : Z ⊓ supportZeroLocus (Ideal.span ({t} : Set R)) ≤
      Z ⊓ supportZeroLocus (Ideal.span ({s * t} : Set R)) :=
    inf_le_inf_left Z (supportZeroLocus_mul_right s t)
  refine ⟨s * t, P.mul_mem hs ht,
    G0WithSupport.enlarge h₁ y + G0WithSupport.enlarge h₂ y', ?_⟩
  rw [map_add]
  have e₁ : G0WithSupport.enlarge inf_le_left (G0WithSupport.enlarge h₁ y) = x := by
    rw [← AddMonoidHom.comp_apply, G0WithSupport.enlarge_comp]
    exact hy
  have e₂ : G0WithSupport.enlarge inf_le_left (G0WithSupport.enlarge h₂ y') = x' := by
    rw [← AddMonoidHom.comp_apply, G0WithSupport.enlarge_comp]
    exact hy'
  rw [e₁, e₂]

lemma mk_torsion (M : SupportedFGModuleOn Z) (h : IsModuleSTorsion P M.obj) :
    HasPrincipalLocalizationSupport P Z (G0WithSupport.mk M) := by
  obtain ⟨s, hs, hM⟩ := exists_annihilator_supportedOn M h
  refine ⟨s, hs, G0WithSupport.mk ⟨M.obj, hM⟩, ?_⟩
  rw [G0WithSupport.enlarge_mk]
end HasPrincipalLocalizationSupport

/-- These elements form a subgroup: products combine the finitely many denominators. -/
def principalLocalizationSupportSubgroup : AddSubgroup (G0WithSupport Z) where
  carrier := {x | HasPrincipalLocalizationSupport P Z x}
  zero_mem' := HasPrincipalLocalizationSupport.zero
  add_mem' := HasPrincipalLocalizationSupport.add
  neg_mem' := HasPrincipalLocalizationSupport.neg

lemma localizationTorsionSubgroup_le_principalSupport :
    localizationTorsionSubgroup P Z ≤ principalLocalizationSupportSubgroup P Z := by
  rw [localizationTorsionSubgroup, AddSubgroup.closure_le]
  rintro x ⟨M, hM, rfl⟩
  exact HasPrincipalLocalizationSupport.mk_torsion M hM


/-- A finite module supported on a principal zero locus is torsion after inversion. -/
lemma moduleSTorsion_of_support_principal {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {s : R} (hs : s ∈ P)
    (h : Module.support R M ⊆ supportZeroLocus (Ideal.span ({s} : Set R))) :
    IsModuleSTorsion P M := by
  change Module.support R M ⊆ PrimeSpectrum.zeroLocus (Ideal.span ({s} : Set R)) at h
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at h
  obtain ⟨n, hn⟩ := h (Ideal.subset_span (Set.mem_singleton s))
  exact fun m => ⟨s ^ n, P.pow_mem hs n, Module.mem_annihilator.mp hn m⟩

namespace G0WithSupport
variable {P Z} {B : Type u} [CommRing B] [Algebra R B] [IsLocalization P B]
  [IsNoetherianRing R]
/-- Every kernel element comes from one closed support cut out by a denominator. -/
lemma localize_kernel_supported (x : G0WithSupport Z)
    (hx : localize (S := B) P Z (supportPullback (algebraMap R B) Z) le_rfl x = 0) :
    ∃ s ∈ P, ∃ y : G0WithSupport (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x := by
  apply localizationTorsionSubgroup_le_principalSupport P Z
  rw [← localize_ker (B := B) P Z]
  exact hx

omit [IsNoetherianRing R] in
/-- The image of a support cut by an inverted element is annihilated by localization. -/
lemma localize_enlarge_principal_eq_zero {s : R} (hs : s ∈ P) :
    (localize (S := B) P Z (supportPullback (algebraMap R B) Z) le_rfl).comp
      (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)) = 0 := by
  apply hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, enlarge_mk, AddMonoidHom.zero_apply]
  apply localize_mk_eq_zero
  exact moduleSTorsion_of_support_principal P hs (fun p hp => (M.property.2 hp).2)

/-- For one element, the supported localization sequence is right exact. -/
lemma localize_away_kernel_range (s : R) [IsLocalization.Away s B] :
    (localize (S := B) (Submonoid.powers s) Z
      (supportPullback (algebraMap R B) Z) le_rfl).ker =
    (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
      from inf_le_left)).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, y, hy⟩ := localize_kernel_supported (P := Submonoid.powers s) (B := B) x hx
    obtain ⟨n, rfl⟩ := ht
    have hm : supportZeroLocus (Ideal.span ({s ^ n} : Set R)) ≤
        supportZeroLocus (Ideal.span ({s} : Set R)) := by
      intro p hp
      change Ideal.span ({s} : Set R) ≤ p.asIdeal
      apply Ideal.span_le.mpr
      intro a ha
      have ha' : a = s := Set.mem_singleton_iff.mp ha
      subst a
      exact p.isPrime.mem_of_pow_mem n (hp (Ideal.subset_span (Set.mem_singleton _)))
    refine ⟨enlarge (inf_le_inf_left Z hm) y, ?_⟩
    rw [← AddMonoidHom.comp_apply, enlarge_comp]
    exact hy
  · rintro x ⟨y, rfl⟩
    exact DFunLike.congr_fun
      (localize_enlarge_principal_eq_zero (P := Submonoid.powers s) (B := B)
        (Submonoid.mem_powers s)) y

end G0WithSupport
end SerrePositivity
