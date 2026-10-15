module
public import Mathlib.RingTheory.Filtration
public import SerrePositivity.HomologicalAlgebra.KoszulCoordinateControl
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulPowers
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Deep images induce zero homology maps by Artin--Rees -/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Artin--Rees controls inverse images along any injection into a finite module. -/
lemma exists_comap_pow_smul_top_le_of_injective
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R N] (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    ∃ c : ℕ, ∀ n : ℕ,
      (I ^ (n + c) • ⊤ : Submodule R N).comap f ≤ I ^ n • ⊤ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨c, fun n => ?_⟩
  apply (Submodule.map_le_map_iff_of_injective hf _ _).mp
  rw [Submodule.map_comap_eq, inf_comm, hc (n + c) (by omega),
    Nat.add_sub_cancel, Submodule.map_smul'', Submodule.map_top]
  exact Submodule.smul_mono le_rfl inf_le_right

/-- A map with ideal-power annihilated target kills cycles lying sufficiently deep in an
ambient finite module. No finiteness condition is imposed on its target. -/
lemma exists_pow_deep_image_killed
    {M N H : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup H]
    [Module R M] [Module R N] [Module R H] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) (q : M →ₗ[R] H)
    (e : ℕ) (he : I ^ e ≤ Module.annihilator R H) :
    ∃ k : ℕ, ∀ x : M, f x ∈ (I ^ k • ⊤ : Submodule R N) → q x = 0 := by
  obtain ⟨c, hc⟩ := exists_comap_pow_smul_top_le_of_injective I f hf
  refine ⟨e + c, fun x hx => ?_⟩
  have hkill : (I ^ e • ⊤ : Submodule R M) ≤ LinearMap.ker q := by
    apply Submodule.smul_le.mpr
    intro a ha y _
    change q (a • y) = 0
    rw [q.map_smul, Module.mem_annihilator.mp (he ha)]
  exact hkill (hc e hx)

/-- For a fixed finite target term whose homology is killed by an ideal power, all complex
maps with sufficiently deep images in that term induce the zero homology map. -/
lemma exists_pow_homologyMap_eq_zero_of_deep_image
    {ι : Type v} {c : ComplexShape ι} (L : HomologicalComplex (ModuleCat.{u} R) c)
    (i : ι) [Module.Finite R (L.X i)] (I : Ideal R) (e : ℕ)
    (he : I ^ e ≤ Module.annihilator R (L.homology i)) :
    ∃ k : ℕ, ∀ (K : HomologicalComplex (ModuleCat.{u} R) c) (f : K ⟶ L),
      LinearMap.range (f.f i).hom ≤ (I ^ k • ⊤ : Submodule R (L.X i)) →
        homologyMap f i = 0 := by
  obtain ⟨k, hk⟩ := exists_pow_deep_image_killed I (L.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) (L.homologyπ i).hom e he
  refine ⟨k, fun K f hf => ?_⟩
  rw [← cancel_epi (K.homologyπ i), comp_zero, homologyπ_naturality]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply hk (cyclesMap f i x)
  have h := hf (LinearMap.mem_range_self (f.f i).hom (K.iCycles i x))
  have heq := congrArg (fun g => g x) (cyclesMap_i f i)
  exact heq.symm ▸ h

/-- For each actual power Koszul stage, sufficiently deep images induce zero maps on its
homology, without any regularity assumption on the parameter sequence. -/
lemma powerKoszul_homologyMap_eq_zero_of_deep_image {e : ℕ} (z : Fin e → R)
    (n : ℕ) (q : ℤ) :
    ∃ k : ℕ, ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
      (f : K ⟶ DerivedCompletion.powerKoszulTower R z n),
      LinearMap.range (f.f q).hom ≤
          (Ideal.span (Set.range z) ^ k • ⊤ : Submodule R
            ((DerivedCompletion.powerKoszulTower R z n).X q)) →
        homologyMap f q = 0 := by
  have h := span_le_annihilator_koszulModuleHomology
    (fun j => z j ^ n) (ModuleCat.of R R) q
  change Ideal.span (Set.range (fun j => z j ^ n)) ≤ Module.annihilator R
    ((koszulComplexOn (fun j => z j ^ n)
      ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj
        (ModuleCat.of R R))).homology q) at h
  rw [koszulComplexOn_single] at h
  obtain ⟨m, hm⟩ := exists_span_pow_le_powerKoszulIdeal z n
  let : Module.Finite R ((DerivedCompletion.powerKoszulTower R z n).X q) :=
    (koszulComplex_free_finite_X (fun j => z j ^ n) q).2
  exact exists_pow_homologyMap_eq_zero_of_deep_image
    (DerivedCompletion.powerKoszulTower R z n) q (Ideal.span (Set.range z)) m (hm.trans h)

end SerrePositivity
