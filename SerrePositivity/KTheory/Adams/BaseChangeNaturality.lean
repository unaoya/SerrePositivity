module

public import SerrePositivity.KTheory.Adams.TensorSquareBaseChangeEigenspaces
public import SerrePositivity.KTheory.Adams.CyclicTwo
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality

/-! # Naturality of the cyclic Adams square under ring change -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Invertible (2 : R)] [Invertible (2 : S)]
namespace Adams
variable (φ : R →+* S)

lemma tensorSquareClass_map
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) :
    K0WithSupport.map φ Z W h (tensorSquareClass P Z hp hs) =
      tensorSquareClass (baseChange φ P) W (strictlyPerfectComplex_baseChange φ P hp)
        ((hs.baseChange φ hp).mono h) := by
  let hp' := strictlyPerfectComplex_baseChange φ P hp
  let hs' := (hs.baseChange φ hp).mono h
  have hpos := K0WithSupport.mk_eq_of_quasiIso W
    (baseChange φ (tensorSquarePositive P)) (tensorSquarePositive (baseChange φ P))
    (strictlyPerfectComplex_baseChange φ _ (tensorSquarePositive_perfect P hp))
    (tensorSquarePositive_perfect _ hp')
    (((tensorSquarePositive_support hp hs).baseChange φ
      (tensorSquarePositive_perfect P hp)).mono h)
    (tensorSquarePositive_support hp' hs') (tensorSquarePositiveBaseChangeIso φ P).hom
  have hneg := K0WithSupport.mk_eq_of_quasiIso W
    (baseChange φ (tensorSquareNegative P)) (tensorSquareNegative (baseChange φ P))
    (strictlyPerfectComplex_baseChange φ _ (tensorSquareNegative_perfect P hp))
    (tensorSquareNegative_perfect _ hp')
    (((tensorSquareNegative_support hp hs).baseChange φ
      (tensorSquareNegative_perfect P hp)).mono h)
    (tensorSquareNegative_support hp' hs') (tensorSquareNegativeBaseChangeIso φ P).hom
  unfold tensorSquareClass CochainInvolution.k0Class
  rw [map_sub, K0WithSupport.map_mk, K0WithSupport.map_mk]
  exact congrArg₂ (fun a b : K0WithSupport W => a - b) hpos hneg

lemma cyclicTwo_map
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport Z) :
    K0WithSupport.map φ Z W h (cyclicTwo Z x) =
      cyclicTwo W (K0WithSupport.map φ Z W h x) := by
  have he : (K0WithSupport.map φ Z W h).comp (cyclicTwo Z) =
      (cyclicTwo W).comp (K0WithSupport.map φ Z W h) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply, cyclicTwo_mk, K0WithSupport.map_mk]
    exact tensorSquareClass_map φ Z W h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity
