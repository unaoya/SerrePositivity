module

public import SerrePositivity.KTheory.Adams.SemilocalPureWeight
public import SerrePositivity.KTheory.K0LocalizationCoefficients

/-! # The Adams weight defect lifts to a support of greater height -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {E : Type v} [CommRing E] {p : ℕ}

lemma LocalizationAdamsFamily.weightDefect_lift (F : LocalizationAdamsFamily R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ) (h : HeightAtLeast Z c)
    (x : K0WithSupport.Coefficients E Z) :
    ∃ s ∈ heightStratumComplement Z c,
      ∃ y : K0WithSupport.Coefficients E
        (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
        HeightAtLeast (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))) (c + 1) ∧
        K0WithSupport.coefficientEnlarge E inf_le_left y =
          F.atBase.operation Z x - (p : E) ^ c • x := by
  let P := heightStratumComplement Z c
  let B := Localization P
  have hl : K0WithSupport.coefficientLocalize (S := B) E P Z
      (F.atBase.operation Z x - (p : E) ^ c • x) = 0 := by
    change K0WithSupport.coefficientMap E (algebraMap R B) Z
      (supportPullback (algebraMap R B) Z) le_rfl
      (F.atBase.operation Z x - (p : E) ^ c • x) = 0
    rw [map_sub, map_smul, F.base_naturality P B,
      F.semilocal_pureWeight Z c h, sub_self]
  obtain ⟨s, hs, y, hy⟩ := K0WithSupport.coefficientLocalize_kernel_supported_of_resolution_contract
    (S := B) E P Z (F.atBase.operation Z x - (p : E) ^ c • x) hl
  exact ⟨s, hs, y, h.cut_succ_of_mem_complement hs, hy⟩

end Adams
end SerrePositivity
