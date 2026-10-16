module
public import Mathlib.RingTheory.LocalRing.Module

/-! # Detecting a finite module comparison with a free target on its original residue fiber -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct

/-- A map from a finite module to a finite free module over a local ring is bijective
if its original residue-field base change is bijective. No source flatness is required. -/
theorem localLinearMap_bijective_of_residue_bijective
    {R M N : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N) (hf : Function.Bijective (f.lTensor (IsLocalRing.ResidueField R))) :
    Function.Bijective f := by
  let K := IsLocalRing.ResidueField R
  have hcomp : Function.Surjective ((TensorProduct.mk R K N 1).comp f) := by
    intro z
    obtain ⟨y, hy⟩ := hf.2 z
    obtain ⟨x, hx⟩ := TensorProduct.mk_surjective R M K Ideal.Quotient.mk_surjective y
    refine ⟨x, ?_⟩
    calc
      (1 : K) ⊗ₜ[R] f x = f.lTensor K ((1 : K) ⊗ₜ[R] x) := rfl
      _ = f.lTensor K y := congrArg (f.lTensor K) hx
      _ = z := hy
  have hrange : f.range.map (TensorProduct.mk R K N 1) = ⊤ := by
    rw [← LinearMap.range_comp, LinearMap.range_eq_top]
    exact hcomp
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp
    (IsLocalRing.map_tensorProduct_mk_eq_top.mp hrange)
  obtain ⟨l, hl⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hf.1
  exact ⟨Function.HasLeftInverse.injective ⟨l, LinearMap.congr_fun hl⟩, hsurj⟩

end SerrePositivity
