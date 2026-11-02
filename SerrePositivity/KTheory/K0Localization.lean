module
public import SerrePositivity.KTheory.Comparison.Basic

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
  let W := Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))
  let V := supportPullback (algebraMap R S) Z
  let hW : W ≤ Z := inf_le_left
  apply AddMonoidHom.exact_iff.mp
  apply (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (enlarge hW) (localize (S := S) (Submonoid.powers s) Z)
    (G0WithSupport.enlarge hW) (G0WithSupport.localize (S := S) (Submonoid.powers s) Z V le_rfl)
    (homologyEuler W) (homologyEuler Z) (homologyEuler V)
    (homologyEuler_enlarge hW).symm
    (homologyEuler_localize (S := S) (Submonoid.powers s) Z).symm
    (k0G0WithSupportEquiv W).surjective (k0G0WithSupportEquiv Z).bijective
    (k0G0WithSupportEquiv V).injective).mpr
  exact AddMonoidHom.exact_iff.mpr (G0WithSupport.localize_away_kernel_range (Z := Z) (B := S) s)

end K0WithSupport
end SerrePositivity
