module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Original kernel and cokernel bounds for finite localization comparisons

The target embeds into a localization of the source. Kernel elements are power
torsion, and a finite target gives one power annihilating the entire cokernel.
These are ordinary module estimates, not almost estimates after perfectoidization.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable {R M N T : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup T] [Module R T]

/-- A pointwise power bound on a finite module has one exponent for the entire module. -/
theorem exists_uniform_power_smul_eq_zero_of_finite [Module.Finite R M]
    (d : R) (h : ∀ x : M, ∃ n : ℕ, d ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, d ^ n • x = 0 := by
  classical
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose k hk using fun j : Fin m => h (s j)
  let n := ∑ j, k j
  let l : M →ₗ[R] M := d ^ n • LinearMap.id
  have hgen : ∀ x ∈ Set.range s, x ∈ l.ker := by
    rintro _ ⟨j, rfl⟩
    change d ^ n • s j = 0
    have hj : k j ≤ n := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    calc
      d ^ n • s j = d ^ (n - k j) • (d ^ k j • s j) := by
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hj]
      _ = 0 := by rw [hk, smul_zero]
  have hfull : (⊤ : Submodule R M) ≤ l.ker := by
    rw [← hs]
    exact Submodule.span_le.mpr hgen
  exact ⟨n, fun x => hfull (Submodule.mem_top)⟩

/-- The kernel of a comparison into its actual localization is pointwise power torsion. -/
theorem localizationComparison_ker_power_torsion
    (d : R) (f : M →ₗ[R] N) (l : M →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] (hcomp : v.comp f = l)
    (x : M) (hx : f x = 0) : ∃ n : ℕ, d ^ n • x = 0 := by
  have hxl : l x = 0 := by
    rw [← hcomp, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (.powers d) l).mp hxl
  obtain ⟨n, hn⟩ := s.2
  change d ^ n = (s : R) at hn
  change (s : R) • x = 0 at hs
  exact ⟨n, by simpa only [← hn] using hs⟩

/-- A finite target embedded in the same localization has a uniformly power-annihilated cokernel. -/
theorem localizationComparison_exists_pow_annihilates_coker [Module.Finite R N]
    (d : R) (f : M →ₗ[R] N) (l : M →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] (hv : Function.Injective v) (hcomp : v.comp f = l) :
    ∃ n : ℕ, ∀ y : N ⧸ f.range, d ^ n • y = 0 := by
  apply exists_uniform_power_smul_eq_zero_of_finite d
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective f.range y
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (.powers d) l (v y)
  have he : (s : R) • y = f x := by
    apply hv
    rw [map_smul]
    rw [← LinearMap.comp_apply, hcomp]
    exact hs
  obtain ⟨n, hn⟩ := s.2
  change d ^ n = (s : R) at hn
  refine ⟨n, ?_⟩
  rw [← map_smul]
  have he' : d ^ n • y = f x := by rw [hn]; exact he
  rw [he']
  exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨x, rfl⟩

/-- Two comparisons into one finite target have one common cokernel exponent. -/
theorem localizationComparisons_exists_common_pow_annihilates_cokers
    {M' : Type u} [AddCommGroup M'] [Module R M'] [Module.Finite R N]
    (d : R) (f : M →ₗ[R] N) (f' : M' →ₗ[R] N)
    (l : M →ₗ[R] T) (l' : M' →ₗ[R] T) (v : N →ₗ[R] T)
    [IsLocalizedModule (.powers d) l] [IsLocalizedModule (.powers d) l']
    (hv : Function.Injective v) (hcomp : v.comp f = l) (hcomp' : v.comp f' = l') :
    ∃ n : ℕ, (∀ y : N ⧸ f.range, d ^ n • y = 0) ∧
      (∀ y : N ⧸ f'.range, d ^ n • y = 0) := by
  obtain ⟨n, hn⟩ := localizationComparison_exists_pow_annihilates_coker d f l v hv hcomp
  obtain ⟨m, hm⟩ := localizationComparison_exists_pow_annihilates_coker d f' l' v hv hcomp'
  refine ⟨n + m, ?_, ?_⟩
  · intro y
    rw [add_comm n m, pow_add, mul_smul, hn, smul_zero]
  · intro y
    rw [pow_add, mul_smul, hm, smul_zero]

end SerrePositivity
