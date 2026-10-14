module

public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedExact
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # Perfectness and support of the low mixed tensor-cube sequence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

lemma tensorCubeLowMixedTarget_perfect
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorCubeLowMixedTarget S) := by
  exact strictlyPerfectComplex_biprod
    (strictlyPerfectComplex_cochainTensor _ _
      (strictlyPerfectComplex_cochainTensor _ _ hd ha) ha)
    (strictlyPerfectComplex_biprod
      (strictlyPerfectComplex_cochainTensor _ _
        (strictlyPerfectComplex_cochainTensor _ _ ha hd) ha)
      (strictlyPerfectComplex_cochainTensor _ _
        (strictlyPerfectComplex_cochainTensor _ _ ha ha) hd))

lemma tensorCubeLowMixedTarget_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorCubeLowMixedTarget S) := by
  exact ((hsD.cochainTensor_left hd S.X₁).cochainTensor_left
      (strictlyPerfectComplex_cochainTensor _ _ hd ha) S.X₁).biprod
    (((hsA.cochainTensor_left ha S.X₃).cochainTensor_left
      (strictlyPerfectComplex_cochainTensor _ _ ha hd) S.X₁).biprod
      ((hsA.cochainTensor_left ha S.X₁).cochainTensor_left
        (strictlyPerfectComplex_cochainTensor _ _ ha ha) S.X₃))

lemma tensorCubeFirstLayer_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hS : S.ShortExact)
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorCubeFirstLayer S.g) := by
  have hT := tensorCubeLowMixedShortComplex_shortExact S hS (fun i => (hd.2 i).2)
  intro n
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hT.homology_exact₂ n)
  exact (module_support_subset_union_of_exact _ _ he).trans
    (Set.union_subset (tensorCube_support ha hsA n)
      (tensorCubeLowMixedTarget_support S ha hd hsA hsD n))

end Adams
end SerrePositivity
