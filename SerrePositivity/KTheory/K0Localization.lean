module
public import SerrePositivity.KTheory.ComparisonNaturality

/-! # Supported K₀ localization and right exactness -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (P : Submonoid R) [IsLocalization P S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  [HasFiniteProjectiveResolutions R] [HasFiniteProjectiveResolutions S]
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

namespace K0WithSupport
/-- Supported localization on K₀, using the existing closed-support base change. -/
def localize (_P : Submonoid R) (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    K0WithSupport Z →+ K0WithSupport (supportPullback (algebraMap R S) Z) :=
  map (algebraMap R S) Z _ le_rfl

omit [IsNoetherianRing R] [IsNoetherianRing S] in
lemma resolutionMap_localize :
    (localize (S := S) P Z).comp (G0WithSupport.resolutionMap Z) =
      (G0WithSupport.resolutionMap (supportPullback (algebraMap R S) Z)).comp
        (G0WithSupport.localize P Z _ le_rfl) := by
  exact G0WithSupport.resolutionMap_map (algebraMap R S)
    (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat S P) Z _ le_rfl

lemma homologyEuler_localize :
    (homologyEuler (supportPullback (algebraMap R S) Z)).comp (localize (S := S) P Z) =
      (G0WithSupport.localize P Z _ le_rfl).comp (homologyEuler Z) := by
  exact homologyEuler_map (algebraMap R S)
    (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat S P) Z _ le_rfl

lemma localize_surjective : Function.Surjective (localize (S := S) P Z) := by
  intro x
  obtain ⟨y, hy⟩ := G0WithSupport.localize_surjective (B := S) P Z
    (homologyEuler (supportPullback (algebraMap R S) Z) x)
  refine ⟨G0WithSupport.resolutionMap Z y, ?_⟩
  have h := DFunLike.congr_fun (resolutionMap_localize (S := S) P Z) y
  change localize P Z (G0WithSupport.resolutionMap Z y) =
    G0WithSupport.resolutionMap _ (G0WithSupport.localize P Z _ le_rfl y) at h
  rw [hy] at h
  exact h.trans (DFunLike.congr_fun (resolutionMap_homologyEuler _) x)

lemma localize_kernel_supported (x : K0WithSupport Z) (hx : localize (S := S) P Z x = 0) :
    ∃ s ∈ P, ∃ y : K0WithSupport (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x := by
  have h := DFunLike.congr_fun (homologyEuler_localize (S := S) P Z) x
  change homologyEuler _ (localize P Z x) =
    G0WithSupport.localize P Z _ le_rfl (homologyEuler Z x) at h
  rw [hx, map_zero] at h
  obtain ⟨s, hs, y, hy⟩ := G0WithSupport.localize_kernel_supported (B := S)
    (homologyEuler Z x) h.symm
  refine ⟨s, hs, G0WithSupport.resolutionMap _ y, ?_⟩
  have he := DFunLike.congr_fun (G0WithSupport.resolutionMap_enlarge
    (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z from inf_le_left)) y
  change enlarge inf_le_left (G0WithSupport.resolutionMap _ y) =
    G0WithSupport.resolutionMap Z (G0WithSupport.enlarge inf_le_left y) at he
  rw [hy] at he
  exact he.trans (DFunLike.congr_fun (resolutionMap_homologyEuler Z) x)

lemma localize_enlarge_principal_eq_zero {s : R} (hs : s ∈ P) :
    (localize (S := S) P Z).comp
      (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)) = 0 := by
  apply AddMonoidHom.ext
  intro y
  apply (k0G0WithSupportEquiv (supportPullback (algebraMap R S) Z)).injective
  have h₁ := DFunLike.congr_fun (homologyEuler_localize (S := S) P Z)
    (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z from inf_le_left) y)
  have h₂ := DFunLike.congr_fun (homologyEuler_enlarge
    (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z from inf_le_left)) y
  change homologyEuler _ (localize P Z (enlarge inf_le_left y)) =
    G0WithSupport.localize P Z _ le_rfl (homologyEuler Z (enlarge inf_le_left y)) at h₁
  change homologyEuler Z (enlarge inf_le_left y) =
    G0WithSupport.enlarge inf_le_left (homologyEuler _ y) at h₂
  rw [h₂] at h₁
  change homologyEuler _ (localize P Z (enlarge inf_le_left y)) = homologyEuler _ 0
  rw [map_zero]
  exact h₁.trans (DFunLike.congr_fun
    (G0WithSupport.localize_enlarge_principal_eq_zero (B := S) (Z := Z) hs) (homologyEuler _ y))

lemma localize_away_kernel_range (s : R) [IsLocalization.Away s S] :
    (localize (S := S) (Submonoid.powers s) Z).ker =
      (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, y, hy⟩ := localize_kernel_supported (S := S) (Submonoid.powers s) Z x hx
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
    exact DFunLike.congr_fun (localize_enlarge_principal_eq_zero (S := S) (Submonoid.powers s) Z
      (Submonoid.mem_powers s)) y
end K0WithSupport
end SerrePositivity
