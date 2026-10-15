module

public import SerrePositivity.KTheory.Adams.Family
public import SerrePositivity.KTheory.CoefficientLinearExtension
public import SerrePositivity.PerfectComplex.IntegerEulerIso

/-! # Pure Adams weight on maximal-ideal support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
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
