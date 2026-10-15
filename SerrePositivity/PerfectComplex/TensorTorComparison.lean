module
public import SerrePositivity.PerfectComplex.TensorAcyclic
public import SerrePositivity.PerfectComplex.IntegerEulerIso
public import SerrePositivity.KTheory.ResolutionClass
public import SerrePositivity.KTheory.ModuleClosedSupport
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.CategoryTheory.AlternatingSum

/-! # Two-sided perfect resolutions compute Tor and intersection multiplicity -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (F : PerfectModuleResolution (ModuleCat.of R M))
    (G : PerfectModuleResolution (ModuleCat.of R N))

/-- Augment the first resolution, leaving the second factor unchanged. -/
def tensorResolutionAugmentation :
    cochainTensor F.complex G.complex ⟶
      cochainTensor (cochainSingleZero (ModuleCat.of R M)) G.complex :=
  cochainTensorMap F.augmentation (𝟙 G.complex)

instance tensorResolutionAugmentation_quasiIso : QuasiIso (tensorResolutionAugmentation F G) :=
  cochainTensor_quasiIso_left_of_perfect G.complex G.perfect F.augmentation

/-- In every degree, the two-sided total tensor agrees with the one-sided resolution model. -/
def tensorResolutionHomologyIso (i : ℤ) :
    (cochainTensor F.complex G.complex).homology i ≅
      (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (.up ℤ)).obj G.complex).homology i :=
  isoOfQuasiIsoAt (tensorResolutionAugmentation F G) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso
      (cochainTensorSingleLeftIso (ModuleCat.of R M) G.complex)

/-- The homology in cochain degree -i of the tensor of perfect resolutions is Tor_i. -/
def tensorResolutionTorIso (i : ℕ) :
    (cochainTensor F.complex G.complex).homology (-(i : ℤ)) ≅
      ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N) :=
  tensorResolutionHomologyIso F G (-(i : ℤ)) ≪≫ (torModuleIsoCochain M G.resolution i).symm

/-- Positive cochain homology vanishes in the two-sided resolution model. -/
lemma tensorResolution_isZero_homology_pos (i : ℤ) (hi : 0 < i) :
    IsZero ((cochainTensor F.complex G.complex).homology i) := by
  have hz : IsZero
      ((((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (.up ℤ)).obj G.complex).X i) :=
    (tensorLeft (ModuleCat.of R M)).map_isZero (G.resolution.isZero_X i hi)
  exact (tensorResolutionHomologyIso F G i).isZero_iff.mpr
    (isZero_homology_of_isZero_X _ _ hz)

/-- The ordinary Euler value of a two-sided tensor of resolutions equals the integer-valued chi. -/
lemma chiOrd_tensorResolution : chiOrd (cochainTensor F.complex G.complex) = (chi R M N : ℝ) := by
  let K := cochainTensor F.complex G.complex
  have hlen (i : ℕ) : Module.length R (K.homology (-(i : ℤ))) = torLength R i M N :=
    (tensorResolutionTorIso F G i).toLinearEquiv.length_eq
  have hz (i : ℤ) (hi : 0 < i) : ((Module.length R (K.homology i)).toNat : ℝ) = 0 := by
    have := ModuleCat.subsingleton_of_isZero (tensorResolution_isZero_homology_pos F G i hi)
    simp [Module.length_eq_zero]
  change (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) *
    ((Module.length R (K.homology i)).toNat : ℝ)) = _
  unfold chi
  apply alternating_finsum_eq_int_cast _ _ hz
  intro i
  simp only [hlen, Int.cast_natCast]

variable [IsNoetherianRing R] [IsLocalRing R]

/-- Integral Euler evaluation of a product of resolution classes is intersection multiplicity. -/
lemma integerEuler_cup_resolutions
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hM : Module.support R M ⊆ Y) (hN : Module.support R N ⊆ Z)
    (hYZ : Y ⊓ Z ≤ supportZeroLocus (IsLocalRing.maximalIdeal R)) :
    K0WithSupport.integerEuler R
      (K0WithSupport.enlarge hYZ (K0WithSupport.cup (F.k0Class Y hM) (G.k0Class Z hN))) =
        chi R M N := by
  let K := cochainTensor F.complex G.complex
  let hp := strictlyPerfectComplex_cochainTensor F.complex G.complex F.perfect G.perfect
  let hs := ((F.support hM).cochainTensor (G.support hN) F.perfect G.perfect).mono hYZ
  have he : K0WithSupport.enlarge hYZ
      (K0WithSupport.cup (F.k0Class Y hM) (G.k0Class Z hN)) =
      K0WithSupport.mk _ (supportedPerfectOnObj _ K hp hs) := by
    simp only [PerfectModuleResolution.k0Class, K0WithSupport.cup_mk_mk,
      K0WithSupport.tensorClass, K0WithSupport.enlarge_mk]
    rfl
  have hreal :
      (K0WithSupport.integerEuler R (K0WithSupport.enlarge hYZ
        (K0WithSupport.cup (F.k0Class Y hM) (G.k0Class Z hN))) : ℝ) = (chi R M N : ℝ) := by
    rw [he, K0WithSupport.integerEuler_mk_complex_real]
    exact chiOrd_tensorResolution F G
  exact_mod_cast hreal

/-- The product is supported at the closed point under the original finite-length hypothesis. -/
lemma integerEuler_cup_resolutions_of_finiteTensor [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (TensorProduct R M N) ≠ ⊤) :
    K0WithSupport.integerEuler R
      (K0WithSupport.enlarge (finiteModuleClosedSupport_inf_le_maximal R M N hfin)
        (K0WithSupport.cup
          (F.k0Class (finiteModuleClosedSupport R M) (support_subset_finiteModuleClosedSupport R M))
          (G.k0Class (finiteModuleClosedSupport R N)
            (support_subset_finiteModuleClosedSupport R N)))) =
      chi R M N :=
  integerEuler_cup_resolutions F G (support_subset_finiteModuleClosedSupport R M)
    (support_subset_finiteModuleClosedSupport R N)
    (finiteModuleClosedSupport_inf_le_maximal R M N hfin)
end SerrePositivity
