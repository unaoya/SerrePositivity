module

public import SerrePositivity.KTheory.Adams.CyclicThree
public import SerrePositivity.PerfectComplex.ClosedSupportFunctoriality

/-! # The cyclic Adams cube commutes with enlargement of support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma tensorCubeClass_enlarge (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) :
    K0WithSupport.coefficientEnlarge E h (tensorCubeClass E t ht ζ P Z hp hs) =
      tensorCubeClass E t ht ζ P W hp (hs.mono h) := by
  unfold tensorCubeClass CochainCubicAction.weightedK0Class
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [K0WithSupport.coefficientEnlarge_tmul]
  apply congrArg (fun x => cubicCharacter ζ j ⊗ₜ[ℤ] x)
  unfold CochainCubicAction.eigenK0Class
  rw [K0WithSupport.enlarge_mk]
  rfl

lemma cyclicThreeValue_enlarge (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (x : K0WithSupport Z) :
    cyclicThreeValue E t ht ζ hζ W (K0WithSupport.enlarge h x) =
      K0WithSupport.coefficientEnlarge E h (cyclicThreeValue E t ht ζ hζ Z x) := by
  have he : (cyclicThreeValue E t ht ζ hζ W).comp (K0WithSupport.enlarge h) =
      (K0WithSupport.coefficientEnlarge E h).toAddMonoidHom.comp
        (cyclicThreeValue E t ht ζ hζ Z) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply, K0WithSupport.enlarge_mk, cyclicThreeValue_mk]
    exact (tensorCubeClass_enlarge E t ht ζ h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)).symm
  exact DFunLike.congr_fun he x

lemma cyclicThree_enlarge (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W)
    (x : K0WithSupport.Coefficients E Z) :
    cyclicThree E t ht ζ hζ W (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h (cyclicThree E t ht ζ hζ Z x) := by
  have he : (cyclicThree E t ht ζ hζ W).comp (K0WithSupport.coefficientEnlarge E h) =
      (K0WithSupport.coefficientEnlarge E h).comp (cyclicThree E t ht ζ hζ Z) := by
    apply coefficientLinearMap_ext E
    intro y
    simp only [LinearMap.comp_apply, K0WithSupport.coefficientEnlarge_tmul,
      cyclicThree_tmul, one_smul, cyclicThreeValue_enlarge E t ht ζ hζ h]
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity
