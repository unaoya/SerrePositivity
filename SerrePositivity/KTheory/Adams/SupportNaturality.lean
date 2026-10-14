module

public import SerrePositivity.KTheory.Adams.KoszulTensor
public import SerrePositivity.PerfectComplex.ClosedSupportFunctoriality

/-! # The cyclic Adams square commutes with enlargement of closed support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace Adams

lemma tensorSquareClass_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    K0WithSupport.enlarge h (tensorSquareClass P Z hp hs) =
      tensorSquareClass P W hp (hs.mono h) := by
  unfold tensorSquareClass CochainInvolution.k0Class
  rw [map_sub, K0WithSupport.enlarge_mk, K0WithSupport.enlarge_mk]
  rfl

lemma cyclicTwo_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (x : K0WithSupport Z) :
    cyclicTwo W (K0WithSupport.enlarge h x) = K0WithSupport.enlarge h (cyclicTwo Z x) := by
  have he : (cyclicTwo W).comp (K0WithSupport.enlarge h) =
      (K0WithSupport.enlarge h).comp (cyclicTwo Z) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply, K0WithSupport.enlarge_mk, cyclicTwo_mk]
    exact (tensorSquareClass_enlarge h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)).symm
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity
