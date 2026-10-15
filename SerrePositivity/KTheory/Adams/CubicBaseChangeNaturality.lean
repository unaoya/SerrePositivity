module

public import SerrePositivity.KTheory.Adams.TensorCubeBaseChangeEigenspaces
public import SerrePositivity.KTheory.Adams.CyclicThree
public import SerrePositivity.PerfectComplex.ClosedSupportFunctoriality

/-! # Naturality of the cyclic Adams cube under root-preserving ring change -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Invertible (3 : R)] [Invertible (3 : S)]
namespace Adams

lemma tensorCubeClass_map (E : Type v) [CommRing E] (φ : R →+* S)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (htS : (φ t) ^ 2 + φ t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) :
    K0WithSupport.coefficientMap E φ Z W h (tensorCubeClass E t ht ζ P Z hp hs) =
      tensorCubeClass E (φ t) htS ζ (baseChange φ P) W
        (strictlyPerfectComplex_baseChange φ P hp) ((hs.baseChange φ hp).mono h) := by
  let hp' := strictlyPerfectComplex_baseChange φ P hp
  let hs' := (hs.baseChange φ hp).mono h
  unfold tensorCubeClass CochainCubicAction.weightedK0Class
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [K0WithSupport.coefficientMap_tmul]
  apply congrArg (fun x => cubicCharacter ζ j ⊗ₜ[ℤ] x)
  let a := (tensorCubeAction P).characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  let b := (tensorCubeAction (baseChange φ P)).characterProjector (φ t)
    (cube_eq_one_of_cubic_relation (φ t) htS) j
  have hpa := a.image_strictlyPerfect (tensorCube_perfect P hp)
  have hpb := b.image_strictlyPerfect (tensorCube_perfect _ hp')
  have hsa := a.image_support (tensorCube_support hp hs)
  have hsb := b.image_support (tensorCube_support hp' hs')
  have he := K0WithSupport.mk_eq_of_quasiIso W (baseChange φ a.image) b.image
    (strictlyPerfectComplex_baseChange φ _ hpa) hpb ((hsa.baseChange φ hpa).mono h) hsb
    (tensorCubeCharacterBaseChangeIso φ P t (cube_eq_one_of_cubic_relation t ht) j).hom
  unfold CochainCubicAction.eigenK0Class
  rw [K0WithSupport.map_mk]
  exact he

lemma cyclicThreeValue_map (E : Type v) [CommRing E] (φ : R →+* S)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (htS : (φ t) ^ 2 + φ t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport Z) :
    K0WithSupport.coefficientMap E φ Z W h (cyclicThreeValue E t ht ζ hζ Z x) =
      cyclicThreeValue E (φ t) htS ζ hζ W (K0WithSupport.map φ Z W h x) := by
  have he : (K0WithSupport.coefficientMap E φ Z W h).toAddMonoidHom.comp
      (cyclicThreeValue E t ht ζ hζ Z) =
      (cyclicThreeValue E (φ t) htS ζ hζ W).comp (K0WithSupport.map φ Z W h) := by
    apply K0WithSupport.hom_ext
    intro X
    simp only [AddMonoidHom.comp_apply,
      cyclicThreeValue_mk, K0WithSupport.map_mk]
    exact tensorCubeClass_map E φ t ht htS ζ Z W h (supportedPerfectRepresentative X)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_support X)
  exact DFunLike.congr_fun he x

lemma cyclicThree_map (E : Type v) [CommRing E] (φ : R →+* S)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (htS : (φ t) ^ 2 + φ t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (x : K0WithSupport.Coefficients E Z) :
    K0WithSupport.coefficientMap E φ Z W h (cyclicThree E t ht ζ hζ Z x) =
      cyclicThree E (φ t) htS ζ hζ W (K0WithSupport.coefficientMap E φ Z W h x) := by
  have he : (K0WithSupport.coefficientMap E φ Z W h).comp (cyclicThree E t ht ζ hζ Z) =
      (cyclicThree E (φ t) htS ζ hζ W).comp (K0WithSupport.coefficientMap E φ Z W h) := by
    apply coefficientLinearMap_ext E
    intro y
    simp only [LinearMap.comp_apply, K0WithSupport.coefficientMap_tmul,
      cyclicThree_tmul, one_smul, cyclicThreeValue_map E φ t ht htS ζ hζ Z W h]
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity
