module

public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import SerrePositivity.KTheory.Adams.Family
public import SerrePositivity.KTheory.CoefficientLinearExtension
public import SerrePositivity.PerfectComplex.IntegerEulerIso
public import SerrePositivity.KTheory.G0.MaximalSupport
public import SerrePositivity.PerfectComplex.CoefficientEuler
public import SerrePositivity.KTheory.K0LocalizationCoefficients
public import SerrePositivity.KTheory.Comparison.Basic
public import SerrePositivity.KTheory.Adams.Weight
public import SerrePositivity.KTheory.Coefficients

/-! # 純粋な Adams の重みと重みの分解

## 概要

素イデアルの局所化の反復を比べ、極大イデアルに台を持つ場合と最小の高さで半局所化した場合に純粋な Adams の重みを示す。係数つきの長さの座標と局所化の結合的な単射性、重みの欠陥の高さの大きい台への持ち上げ、重みの多項式が台つき K₀ を消すこと、有限次元の仮定なしの有限な重みの分解、高さの和からのカップ積の消滅を与える。

## 方針

高さについての帰納法：最小の高さで半局所化して純粋な重みを示し、欠陥を高さの大きい台へ持ち上げる。

## 規約

有限次元の仮定は置かない。

## 使われ方

交点重複度の消滅（IntersectionMultiplicity/Vanishing）。
-/

@[expose] public noncomputable section

universe u v

section IteratedPrimeLocalizationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
namespace Adams
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Comparison as an R-algebra, retaining the composed structure map. -/
def iteratedPrimeLocalizationEquiv (P : Submonoid R) [IsLocalization P B]
    (q : PrimeSpectrum B) :
    letI : Algebra R (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp (algebraMap R B)).toAlgebra
    Localization.AtPrime (PrimeSpectrum.comap (algebraMap R B) q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal := by
  let T := Localization.AtPrime q.asIdeal
  letI : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  letI : SMul R T := (inferInstance : Algebra R T).toSMul
  letI : SMul B T := (inferInstance : Algebra B T).toSMul
  letI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization.AtPrime T (PrimeSpectrum.comap (algebraMap R B) q).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization P T q.asIdeal
  exact IsLocalization.algEquiv
    (PrimeSpectrum.comap (algebraMap R B) q).asIdeal.primeCompl
    (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R B) q).asIdeal) T

/-- A prime localization of any localization of a regular local ring is regular;
its dimension is the height of its contracted prime. -/
lemma iteratedPrime_regular_dimension [IsRegularLocalRing R]
    (P : Submonoid R) [IsLocalization P B] (q : PrimeSpectrum B) (c : ℕ)
    (hc : (PrimeSpectrum.comap (algebraMap R B) q).asIdeal.height = (c : ℕ∞)) :
    IsRegularLocalRing (Localization.AtPrime q.asIdeal) ∧
      ringKrullDim (Localization.AtPrime q.asIdeal) = c := by
  let T := Localization.AtPrime q.asIdeal
  let : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : SMul B T := (inferInstance : Algebra B T).toSMul
  let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime T (PrimeSpectrum.comap (algebraMap R B) q).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization P T q.asIdeal
  refine ⟨isRegularLocalRing_atPrime (PrimeSpectrum.comap (algebraMap R B) q) T, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (PrimeSpectrum.comap (algebraMap R B) q).asIdeal T, hc]
  rfl

end Adams
end SerrePositivity

end IteratedPrimeLocalizationPart

section MaximalPureWeightPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open TensorProduct IsLocalRing CategoryTheory
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {E : Type v} [CommRing E] {p : ℕ}
namespace Adams

omit [IsNoetherianRing R] in
lemma maximalParameterKoszulClass {n : ℕ} (z : Fin n → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) :
    maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z)) =
      K0WithSupport.enlarge
        (le_of_eq (show koszulClosedSupport z = supportZeroLocus (maximalIdeal R) from
          congrArg supportZeroLocus hz)) (koszulClass z) := by
  simp only [maximalFreeClosedSupportEquiv, AddEquiv.trans_apply,
    freeClosedSupportK0Equiv_apply, freeToClosedSupportK0_mk, K0WithSupport.congr_mk,
    koszulClass, K0WithSupport.enlarge_mk]
  apply K0WithSupport.mk_iso _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ ?_))
  rw [supportedPerfectOnCongr_obj]
  exact Iso.refl _

namespace SupportedAdams

lemma maximal_pureWeight_of_parameters (A : SupportedAdams R E p) {n : ℕ}
    (z : Fin n → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (hK : IsKoszulResolution z)
    (x : K0WithSupport.Coefficients E (supportZeroLocus (maximalIdeal R))) :
    A.operation (supportZeroLocus (maximalIdeal R)) x = (p : E) ^ n • x := by
  let Z := supportZeroLocus (maximalIdeal R)
  let η : K0WithSupport Z →+ K0WithSupport.Coefficients E Z :=
    (TensorProduct.mk ℤ E (K0WithSupport Z) (1 : E)).toAddMonoidHom
  let f := (A.operation Z).toAddMonoidHom.comp η
  let g := (((p : E) ^ n •
    (LinearMap.id : K0WithSupport.Coefficients E Z →ₗ[E]
      K0WithSupport.Coefficients E Z)).toAddMonoidHom).comp η
  have hg : f (maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z))) =
      g (maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z))) := by
    change A.operation Z ((1 : E) ⊗ₜ[ℤ]
        maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z))) =
      (p : E) ^ n • ((1 : E) ⊗ₜ[ℤ]
        maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z)))
    rw [maximalParameterKoszulClass z hz, ← K0WithSupport.coefficientEnlarge_tmul,
      A.enlarge, A.koszul, map_smul]
  have he : f = g := maximalSupport_hom_ext_koszul z hz hK hg
  have he' : A.operation Z = (p : E) ^ n • LinearMap.id :=
    coefficientLinearMap_ext E _ _ (fun y => DFunLike.congr_fun he y)
  exact DFunLike.congr_fun he' x

/-- On maximal-ideal support the weight is the dimension, including dimension zero. -/
lemma maximal_pureWeight {T : Type u} [CommRing T] [IsRegularLocalRing T]
    (A : SupportedAdams T E p) (d : ℕ) (hd : ringKrullDim T = d)
    (x : K0WithSupport.Coefficients E (supportZeroLocus (maximalIdeal T))) :
    A.operation (supportZeroLocus (maximalIdeal T)) x = (p : E) ^ d • x := by
  obtain ⟨n, z, hz, hreg, hdim⟩ := exists_regular_generators_fin T
  have hn : n = d := by exact_mod_cast hdim.symm.trans hd
  rw [← hn]
  exact A.maximal_pureWeight_of_parameters z hz
    (isKoszulResolution_of_isWeaklyRegular z hreg) x

end SupportedAdams
end Adams
end SerrePositivity

end MaximalPureWeightPart

section CoefficientLengthEquivPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open TensorProduct IsLocalRing
namespace Adams
variable (E : Type v) [CommRing E] {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (W : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hw : ∀ p ∈ W, p.asIdeal.IsMaximal)
variable [Fintype {p : PrimeSpectrum R // p ∈ W}]

variable [HasFiniteProjectiveResolutions R]

def coefficientK0LengthEquiv : K0WithSupport.Coefficients E W ≃ₗ[E]
    ({p : PrimeSpectrum R // p ∈ W} → E) :=
  ((k0G0WithSupportEquiv W).toIntLinearEquiv.baseChange ℤ E _ _) ≪≫ₗ
    coefficientG0LengthEquiv E W hw

lemma coefficientK0LengthEquiv_tmul (a : E) (x : K0WithSupport W)
    (p : {p : PrimeSpectrum R // p ∈ W}) :
    coefficientK0LengthEquiv E W hw (a ⊗ₜ[ℤ] x) p =
      a * (localLengthMap W hw p.val (K0WithSupport.homologyEuler W x) : E) := by
  change coefficientG0LengthEquiv E W hw
    (a ⊗ₜ[ℤ] K0WithSupport.homologyEuler W x) p = _
  exact coefficientG0LengthEquiv_tmul E W hw a _ p

omit [Fintype {p : PrimeSpectrum R // p ∈ W}] in
lemma localLengthMap_homologyEuler (p : PrimeSpectrum R) (x : K0WithSupport W) :
    localLengthMap W hw p (K0WithSupport.homologyEuler W x) =
      K0WithSupport.integerEuler (Localization.AtPrime p.asIdeal)
        (K0WithSupport.map (algebraMap R (Localization.AtPrime p.asIdeal)) W
          (supportZeroLocus (maximalIdeal (Localization.AtPrime p.asIdeal)))
          (maximalSupport_pullback_le W hw p) x) := by
  let T := Localization.AtPrime p.asIdeal
  let := hasFiniteProjectiveResolutions_of_localization (S := T) p.asIdeal.primeCompl
  have he := DFunLike.congr_fun (K0WithSupport.homologyEuler_map (algebraMap R T)
    (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat T p.asIdeal.primeCompl)
    W (supportZeroLocus (maximalIdeal T)) (maximalSupport_pullback_le W hw p)) x
  exact congrArg (maximalSupportLengthMap T) he.symm

lemma coefficientK0LengthEquiv_apply_local (x : K0WithSupport.Coefficients E W)
    (p : {p : PrimeSpectrum R // p ∈ W}) :
    coefficientK0LengthEquiv E W hw x p =
      K0WithSupport.coefficientEuler E (Localization.AtPrime p.val.asIdeal)
        (K0WithSupport.coefficientMap E (algebraMap R (Localization.AtPrime p.val.asIdeal)) W
          (supportZeroLocus (maximalIdeal (Localization.AtPrime p.val.asIdeal)))
          (maximalSupport_pullback_le W hw p.val) x) := by
  have he : (LinearMap.proj p).comp (coefficientK0LengthEquiv E W hw).toLinearMap =
      (K0WithSupport.coefficientEuler E (Localization.AtPrime p.val.asIdeal)).comp
        (K0WithSupport.coefficientMap E (algebraMap R (Localization.AtPrime p.val.asIdeal)) W
          (supportZeroLocus (maximalIdeal (Localization.AtPrime p.val.asIdeal)))
          (maximalSupport_pullback_le W hw p.val)) := by
    apply coefficientLinearMap_ext E
    intro y
    change coefficientK0LengthEquiv E W hw ((1 : E) ⊗ₜ[ℤ] y) p = _
    rw [coefficientK0LengthEquiv_tmul, LinearMap.comp_apply,
      K0WithSupport.coefficientMap_tmul, K0WithSupport.coefficientEuler_tmul,
      localLengthMap_homologyEuler]
  exact DFunLike.congr_fun he x

omit [Fintype {p : PrimeSpectrum R // p ∈ W}] in
/-- Joint localizations detect zero on finite maximal support with any coefficients. -/
lemma coefficient_eq_zero_of_localizations [Finite {p : PrimeSpectrum R // p ∈ W}]
    (x : K0WithSupport.Coefficients E W)
    (hx : ∀ p : {p : PrimeSpectrum R // p ∈ W},
      K0WithSupport.coefficientMap E (algebraMap R (Localization.AtPrime p.val.asIdeal)) W
        (supportZeroLocus (maximalIdeal (Localization.AtPrime p.val.asIdeal)))
        (maximalSupport_pullback_le W hw p.val) x = 0) : x = 0 := by
  letI := Fintype.ofFinite {p : PrimeSpectrum R // p ∈ W}
  apply (coefficientK0LengthEquiv E W hw).injective
  rw [map_zero]
  funext p
  rw [coefficientK0LengthEquiv_apply_local, hx, map_zero]
  rfl

end Adams
end SerrePositivity

end CoefficientLengthEquivPart

section SemilocalPureWeightPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open IsLocalRing
namespace Adams
variable {R B : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing B] [Algebra R B]
variable {E : Type v} [CommRing E] {p : ℕ}
variable (F : LocalizationAdamsFamily R E p)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ)
variable [IsLocalization (heightStratumComplement Z c) B]

/-- On the least-height support in the semilocal ring, the operation is p^c. -/
lemma LocalizationAdamsFamily.semilocal_pureWeight (h : HeightAtLeast Z c)
    (x : K0WithSupport.Coefficients E (supportPullback (algebraMap R B) Z)) :
    (F.atLocalization (heightStratumComplement Z c) B).operation
        (supportPullback (algebraMap R B) Z) x = (p : E) ^ c • x := by
  let W := supportPullback (algebraMap R B) Z
  let hw : ∀ q ∈ W, q.asIdeal.IsMaximal := fun q hq => (h.mem_pullback_iff_isMaximal q).mp hq
  let := IsLocalization.isNoetherianRing (heightStratumComplement Z c) B
    (inferInstance : IsNoetherianRing R)
  let := hasFiniteProjectiveResolutions_of_localization (S := B) (heightStratumComplement Z c)
  have hf : (W : Set (PrimeSpectrum B)).Finite :=
    h.finite_localized_maximal_points.subset (fun q hq => (h.mem_pullback_iff_isMax q).mp hq)
  let := hf.fintype
  apply sub_eq_zero.mp
  apply coefficient_eq_zero_of_localizations E W hw
  intro q
  let T := Localization.AtPrime q.val.asIdeal
  let r := PrimeSpectrum.comap (algebraMap R B) q.val
  let : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : SMul B T := (inferInstance : Algebra B T).toSMul
  let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime T r.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (heightStratumComplement Z c) T q.val.asIdeal
  have hr : r.asIdeal.height = (c : ℕ∞) :=
    ((h.mem_pullback_iff_heightStratum q.val).mp q.property).2
  obtain ⟨hregular, hd⟩ := iteratedPrime_regular_dimension
    (heightStratumComplement Z c) q.val c hr
  let := hregular
  let ht := maximalSupport_pullback_le W hw q.val
  have hn := F.localization_naturality (heightStratumComplement Z c) r.asIdeal.primeCompl B T
    (algebraMap B T) (IsScalarTower.algebraMap_eq R B T).symm
    W (supportZeroLocus (maximalIdeal T)) ht x
  have hpure := (F.atLocalization r.asIdeal.primeCompl T).maximal_pureWeight c hd
    (K0WithSupport.coefficientMap E (algebraMap B T) W
      (supportZeroLocus (maximalIdeal T)) ht x)
  rw [map_sub, map_smul, hn, hpure, sub_self]

end Adams
end SerrePositivity

end SemilocalPureWeightPart

section WeightDefectLiftPart

set_option backward.isDefEq.respectTransparency false
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

end WeightDefectLiftPart

section WeightAnnihilationPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open TensorProduct Polynomial
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [CommRing E]

lemma coefficient_empty_zero (x : K0WithSupport.Coefficients E
    (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) : x = 0 :=
  K0WithSupport.coefficient_eq_zero_of_empty_support E x

variable [IsRegularLocalRing R] {p : ℕ}

/-- The proof descends in the height bound and quantifies over all closed supports. -/
lemma LocalizationAdamsFamily.weightPolynomial_annihilates (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d + 1)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (x : K0WithSupport.Coefficients E Z) :
    (aeval (F.atBase.operation Z) (weightPolynomial E p c d)) x = 0 := by
  refine Nat.decreasingInduction (motive := fun c _ =>
    ∀ Z : TopologicalSpace.Closeds (PrimeSpectrum R), HeightAtLeast Z c →
      ∀ x : K0WithSupport.Coefficients E Z,
        (aeval (F.atBase.operation Z) (weightPolynomial E p c d)) x = 0) ?_ ?_ hc Z hz x
  · intro c hc ih Z hz x
    rw [weightPolynomial_succ E p c d (by omega), map_mul, Module.End.mul_apply]
    simp only [map_sub, aeval_X, aeval_C]
    change (aeval (F.atBase.operation Z) (weightPolynomial E p (c + 1) d))
      (F.atBase.operation Z x - (p : E) ^ c • x) = 0
    obtain ⟨s, _, y, hheight, hy⟩ := F.weightDefect_lift Z c hz x
    rw [← hy, F.atBase.polynomial_enlarge, ih _ hheight y, map_zero]
  · intro Z hz x
    have he := hz.eq_bot_of_dimension_bound hd
    subst Z
    rw [coefficient_empty_zero x, map_zero]

end Adams
end SerrePositivity

end WeightAnnihilationPart

section WeightDecompositionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [Field E] [CharZero E] {p : ℕ}

variable [IsRegularLocalRing R]

omit [CharZero E] in
lemma LocalizationAdamsFamily.weightProjector_eigen (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (j : ℕ) (hj : j ∈ Finset.Icc c d) (x : K0WithSupport.Coefficients E Z) :
    F.atBase.operation Z (F.atBase.weightProjector Z c d j x) =
      (p : E) ^ j • F.atBase.weightProjector Z c d j x :=
  lagrangeProjector_eigen _ _ _ j hj x
    (F.weightPolynomial_annihilates d hd c (by omega) Z hz x)

lemma LocalizationAdamsFamily.weightProjector_idem (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (j : ℕ) (hj : j ∈ Finset.Icc c d) :
    F.atBase.weightProjector Z c d j * F.atBase.weightProjector Z c d j =
      F.atBase.weightProjector Z c d j :=
  lagrangeProjector_idem _ _ _ (natPow_injective (E := E) F.atBase.two_le).injOn j hj
    (fun x => F.weightPolynomial_annihilates d hd c (by omega) Z hz x)

omit [CharZero E] in
lemma LocalizationAdamsFamily.weightProjector_orthogonal (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ) (hc : c ≤ d)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (i j : ℕ) (hj : j ∈ Finset.Icc c d) (hne : i ≠ j) :
    F.atBase.weightProjector Z c d i * F.atBase.weightProjector Z c d j = 0 :=
  lagrangeProjector_orthogonal _ _ _ i j hj hne
    (fun x => F.weightPolynomial_annihilates d hd c (by omega) Z hz x)

/-- Every class has a finite weight decomposition; an empty interval forces the class to zero. -/
lemma LocalizationAdamsFamily.weightDecomposition (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R ≤ d) (c : ℕ)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hz : HeightAtLeast Z c)
    (x : K0WithSupport.Coefficients E Z) :
    (∑ j ∈ Finset.Icc c d, F.atBase.weightProjector Z c d j x) = x ∧
      ∀ j ∈ Finset.Icc c d, F.atBase.operation Z (F.atBase.weightProjector Z c d j x) =
        (p : E) ^ j • F.atBase.weightProjector Z c d j x := by
  constructor
  · by_cases hc : c ≤ d
    · exact F.atBase.sum_weightProjector Z c d hc x
    · have hheight : HeightAtLeast Z (d + 1) := by
        intro q hq
        exact (Nat.cast_le.mpr (show d + 1 ≤ c by omega)).trans (hz q hq)
      have he := hheight.eq_bot_of_dimension_bound hd
      subst Z
      rw [coefficient_empty_zero x]
      simp only [map_zero, Finset.sum_const_zero]
  · intro j hj
    have hc : c ≤ d := (Finset.mem_Icc.mp hj).1.trans (Finset.mem_Icc.mp hj).2
    exact F.weightProjector_eigen d hd c hc Z hz j hj x

end Adams
end SerrePositivity

end WeightDecompositionPart

section CupVanishingPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open IsLocalRing
namespace Adams
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {E : Type v} [Field E] [CharZero E] {p : ℕ}

/-- A product of eigenclasses vanishes when its weight differs from the dimension. -/
lemma SupportedAdams.cup_enlarge_eq_zero_of_eigen (A : SupportedAdams R E p)
    (d : ℕ) (hd : ringKrullDim R = d)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Y ⊓ Z ≤ supportZeroLocus (maximalIdeal R)) (i j : ℕ)
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z)
    (hx : A.operation Y x = (p : E) ^ i • x)
    (hy : A.operation Z y = (p : E) ^ j • y) (hne : i + j ≠ d) :
    K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y) = 0 :=
  A.eigen_eq_zero_of_weight_ne _ (i + j) d _
    (A.cup_enlarge_eigen h i j x y hx hy) (A.maximal_pureWeight d hd _) hne

/-- High-weight products vanish after enlargement to maximal-ideal support. -/
lemma LocalizationAdamsFamily.cup_enlarge_eq_zero (F : LocalizationAdamsFamily R E p)
    (d : ℕ) (hd : ringKrullDim R = d)
    (Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (cY cZ : ℕ)
    (hY : HeightAtLeast Y cY) (hZ : HeightAtLeast Z cZ) (hc : d < cY + cZ)
    (h : Y ⊓ Z ≤ supportZeroLocus (maximalIdeal R))
    (x : K0WithSupport.Coefficients E Y) (y : K0WithSupport.Coefficients E Z) :
    K0WithSupport.coefficientEnlarge E h (K0WithSupport.coefficientCup E x y) = 0 := by
  have hx := F.weightDecomposition d hd.le cY Y hY x
  have hy := F.weightDecomposition d hd.le cZ Z hZ y
  have hterm : ∀ i ∈ Finset.Icc cY d, ∀ j ∈ Finset.Icc cZ d,
      K0WithSupport.coefficientEnlarge E h
        (K0WithSupport.coefficientCup E (F.atBase.weightProjector Y cY d i x)
          (F.atBase.weightProjector Z cZ d j y)) = 0 := by
    intro i hi j hj
    apply F.atBase.cup_enlarge_eq_zero_of_eigen d hd h i j _ _ (hx.2 i hi) (hy.2 j hj)
    have hi' := (Finset.mem_Icc.mp hi).1
    have hj' := (Finset.mem_Icc.mp hj).1
    omega
  rw [← hx.1, ← hy.1]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  exact hterm i hi j hj

end Adams
end SerrePositivity

end CupVanishingPart
