module
public import SerrePositivity.PerfectComplex.IntegerEuler
public import SerrePositivity.PerfectComplex.ClosedSupport.K0
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic

/-! # The integer Euler isomorphism at the maximal ideal -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits IsLocalRing
variable {R : Type u} [CommRing R]

variable [IsNoetherianRing R] [IsLocalRing R] {n : ℕ} (z : Fin n → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R)

/-- Transfer the existing finite-free model to the maximal-ideal support. -/
def maximalFreeClosedSupportEquiv : K0Supported R z ≃+
    K0WithSupport (supportZeroLocus (maximalIdeal R)) :=
  (freeClosedSupportK0Equiv z).trans (K0WithSupport.congr (congrArg supportZeroLocus hz))

/-- The integer Euler map on the image of a finite-free supported complex computes chiOrd. -/
lemma maximalFreeClosedSupportEquiv_euler_real (P : PerfSupp R z) :
    (K0WithSupport.integerEuler R (maximalFreeClosedSupportEquiv z hz (K0.mk P)) : ℝ) =
      chiOrd P.1 := by
  rw [maximalFreeClosedSupportEquiv, AddEquiv.trans_apply,
    freeClosedSupportK0Equiv_apply, freeToClosedSupportK0_mk, K0WithSupport.congr_mk]
  apply K0WithSupport.integerEuler_mk_real_of_rep
  rw [supportedPerfectOnCongr_obj]
  rfl

/-- The image of the parameter Koszul complex has integer Euler value one. -/
lemma maximalFreeClosedSupportEquiv_koszul_euler (hK : IsKoszulResolution z) :
    K0WithSupport.integerEuler R
      (maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z))) = 1 := by
  have h := maximalFreeClosedSupportEquiv_euler_real z hz (koszulPerfSupp z)
  change (_ : ℝ) = chiOrd (koszulComplex z) at h
  rw [chiOrd_koszulComplex hK hz] at h
  exact_mod_cast h

/-- A parameter Koszul class generates the maximal-ideal supported K₀. -/
lemma maximalSupport_hom_ext_koszul (hK : IsKoszulResolution z)
    {A : Type*} [AddCommGroup A]
    {f g : K0WithSupport (supportZeroLocus (maximalIdeal R)) →+ A}
    (h : f (maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z))) =
      g (maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z)))) : f = g := by
  have he : f.comp (maximalFreeClosedSupportEquiv z hz).toAddMonoidHom =
      g.comp (maximalFreeClosedSupportEquiv z hz).toAddMonoidHom :=
    K0.hom_ext_koszul hz hK h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (maximalFreeClosedSupportEquiv z hz).surjective x
  exact DFunLike.congr_fun he y

/-- The integer Euler isomorphism for a specified regular parameter sequence. -/
def maximalSupportIntegerEulerEquivOfParameters (hK : IsKoszulResolution z) :
    K0WithSupport (supportZeroLocus (maximalIdeal R)) ≃+ ℤ := by
  let K := maximalFreeClosedSupportEquiv z hz (K0.mk (koszulPerfSupp z))
  let f : ℤ →+ K0WithSupport (supportZeroLocus (maximalIdeal R)) :=
    { toFun := fun n => n • K
      map_zero' := zero_zsmul K
      map_add' := fun a b => add_zsmul K a b }
  have hK1 : K0WithSupport.integerEuler R K = 1 :=
    maximalFreeClosedSupportEquiv_koszul_euler z hz hK
  have hleft : f.comp (K0WithSupport.integerEuler R) = AddMonoidHom.id _ := by
    apply maximalSupport_hom_ext_koszul z hz hK
    change (K0WithSupport.integerEuler R K) • K = K
    rw [hK1, one_zsmul]
  have hright : (K0WithSupport.integerEuler R).comp f = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro n
    change K0WithSupport.integerEuler R (n • K) = n
    rw [map_zsmul, hK1]
    simp
  exact
    { toFun := K0WithSupport.integerEuler R
      invFun := f
      left_inv := fun x => DFunLike.congr_fun hleft x
      right_inv := fun n => DFunLike.congr_fun hright n
      map_add' := (K0WithSupport.integerEuler R).map_add }

lemma maximalSupportIntegerEulerEquivOfParameters_apply (hK : IsKoszulResolution z)
    (x : K0WithSupport (supportZeroLocus (maximalIdeal R))) :
    maximalSupportIntegerEulerEquivOfParameters z hz hK x =
      K0WithSupport.integerEuler R x := rfl


namespace K0WithSupport
variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- A regular local ring admits an Euler equivalence with the prescribed forward map. -/
lemma exists_integerEulerEquiv :
    ∃ e : K0WithSupport (supportZeroLocus (maximalIdeal R)) ≃+ ℤ,
      ∀ x, e x = integerEuler R x := by
  obtain ⟨_, z, hz, hreg, _⟩ := exists_regular_generators_fin R
  let hK := isKoszulResolution_of_isWeaklyRegular z hreg
  exact ⟨maximalSupportIntegerEulerEquivOfParameters z hz hK, fun _ => rfl⟩

/-- Integer Euler is an additive equivalence at the maximal ideal of a regular local ring. -/
def integerEulerEquiv : K0WithSupport (supportZeroLocus (maximalIdeal R)) ≃+ ℤ :=
  Classical.choose (exists_integerEulerEquiv R)

@[simp]
lemma integerEulerEquiv_apply (x : K0WithSupport (supportZeroLocus (maximalIdeal R))) :
    integerEulerEquiv R x = integerEuler R x :=
  Classical.choose_spec (exists_integerEulerEquiv R) x

lemma integerEulerEquiv_toAddMonoidHom :
    (integerEulerEquiv R).toAddMonoidHom = integerEuler R := by
  apply AddMonoidHom.ext
  intro x
  exact integerEulerEquiv_apply R x

/-- Euler detects zero integrally, before any extension of coefficients. -/
lemma integerEuler_eq_zero_iff (x : K0WithSupport (supportZeroLocus (maximalIdeal R))) :
    integerEuler R x = 0 ↔ x = 0 := by
  rw [← integerEulerEquiv_apply R x]
  exact (integerEulerEquiv R).map_eq_zero_iff
end K0WithSupport
end SerrePositivity
