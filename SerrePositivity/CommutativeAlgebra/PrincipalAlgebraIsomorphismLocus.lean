module
public import SerrePositivity.CommutativeAlgebra.FiniteAlgebraLocalizationLift
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Shrinking a principal algebra comparison to an actual algebra isomorphism -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

private lemma localizedTensorMap_eq_lTensor
    {R S X Y : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (M : Submonoid R) [IsLocalization M S] (u : X →ₗ[R] Y) :
    IsLocalizedModule.map M (TensorProduct.mk R S X 1) (TensorProduct.mk R S Y 1) u =
      u.lTensor S := by
  apply IsLocalizedModule.ext M (TensorProduct.mk R S X 1)
    (IsLocalizedModule.map_units (TensorProduct.mk R S Y 1))
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [IsLocalizedModule.map_apply]
  rfl

/-- An algebra comparison whose stalk is the specified finite product can be made an
actual algebra isomorphism on a smaller principal neighborhood. The value on every
original coefficient is retained, including when the rank is zero. -/
theorem principalAlgebraComparison_exists_algEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A] (p : Ideal R) [p.IsPrime]
    (d : R) (hd : d ∉ p) (r : ℕ)
    (ψ : A →ₐ[R] (Fin r → Localization.Away d))
    (e : (Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
      (Fin r → Localization.AtPrime p))
    (hψ : ∀ a i, IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R (Localization.AtPrime p))
      (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨d, hd⟩)
        (ψ a i) = e ((1 : Localization.AtPrime p) ⊗ₜ[R] a) i) :
    ∃ (g : R) (hg : g ∉ p) (hdg : d ∣ g)
      (E : (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
        (Fin r → Localization.Away g)),
      ∀ a i, E ((1 : Localization.Away g) ⊗ₜ[R] a) i =
        IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R (Localization.Away g))
          (isUnit_of_dvd_unit (map_dvd (algebraMap R (Localization.Away g)) hdg)
            (IsLocalization.Away.algebraMap_isUnit g)) (ψ a i) := by
  classical
  let L := Localization.Away d
  let S := Localization.AtPrime p
  let F := Fin r → R
  let qL := TensorProduct.piScalarRight R L L (Fin r)
  let fL : F →ₗ[R] (Fin r → L) :=
    (qL.restrictScalars R).toLinearMap.comp (TensorProduct.mk R L F 1)
  letI : IsLocalizedModule (.powers d) fL :=
    IsLocalizedModule.of_linearEquiv (.powers d) (TensorProduct.mk R L F 1) (qL.restrictScalars R)
  obtain ⟨u, s, hu⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (.powers d) fL ψ.toLinearMap
  have hu' (a : A) (i : Fin r) : algebraMap R L (u a i) =
      algebraMap R L (s : R) * ψ a i := by
    have hh := congrArg (fun v : Fin r → L => v i) (LinearMap.congr_fun hu a)
    change (u a i) • (1 : L) = (s : R) • ψ a i at hh
    simpa only [Algebra.smul_def, mul_one] using hh
  let α : L →ₐ[R] S := IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R S)
    (IsLocalization.map_units (M := p.primeCompl) S ⟨d, hd⟩)
  have huS (a : A) (i : Fin r) : algebraMap R S (u a i) =
      algebraMap R S (s : R) * e ((1 : S) ⊗ₜ[R] a) i := by
    have hh := congrArg α (hu' a i)
    rw [map_mul, α.commutes, α.commutes, hψ] at hh
    exact hh
  have hle : Submonoid.powers d ≤ p.primeCompl := Submonoid.powers_le.mpr hd
  have hsS : IsUnit (algebraMap R S (s : R)) :=
    IsLocalization.map_units S (⟨s, hle s.2⟩ : p.primeCompl)
  let qS := TensorProduct.piScalarRight R S S (Fin r)
  have hcommS (z : S ⊗[R] A) : qS (u.lTensor S z) = algebraMap R S (s : R) • e z := by
    induction z using TensorProduct.inductionOn with
    | tmul k a =>
      ext i
      change (u a i) • k = algebraMap R S (s : R) * e (k ⊗ₜ[R] a) i
      rw [Algebra.smul_def, huS]
      have hk : k ⊗ₜ[R] a = k • ((1 : S) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hk, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hbijS : Function.Bijective (u.lTensor S) := by
    have hb : Function.Bijective (fun z : S ⊗[R] A => qS (u.lTensor S z)) := by
      have hh := hsS.smul_bijective.comp e.bijective
      simpa only [Function.comp_def, ← hcommS] using hh
    constructor
    · intro x y hxy
      exact hb.1 (congrArg qS hxy)
    · intro y
      obtain ⟨x, hx⟩ := hb.2 (qS y)
      exact ⟨x, qS.injective hx⟩
  have hm : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (TensorProduct.mk R S A 1) (TensorProduct.mk R S F 1) u) := by
    rw [localizedTensorMap_eq_lTensor]
    exact hbijS
  obtain ⟨b, hb, hb'⟩ := exists_bijective_map_powers p.primeCompl
    (TensorProduct.mk R S A 1) (TensorProduct.mk R S F 1) u hm
  let g := d * b
  have hg : g ∉ p := p.primeCompl.mul_mem hd hb
  have hdg : d ∣ g := dvd_mul_right d b
  let V := Localization.Away g
  let β : L →ₐ[R] V := IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R V)
    (isUnit_of_dvd_unit (map_dvd (algebraMap R V) hdg) (IsLocalization.Away.algebraMap_isUnit g))
  let ψV : A →ₐ[R] (Fin r → V) := AlgHom.pi (fun i =>
    β.comp ((Pi.evalAlgHom R (fun _ : Fin r => L) i).comp ψ))
  let EV : V ⊗[R] A →ₐ[V] (Fin r → V) := (AlgHom.liftEquiv R V A (Fin r → V)) ψV
  have hsV : IsUnit (algebraMap R V (s : R)) := by
    have hh := (IsLocalization.map_units L s).map β.toRingHom
    change IsUnit (β (algebraMap R L (s : R))) at hh
    rw [β.commutes] at hh
    exact hh
  let qV := TensorProduct.piScalarRight R V V (Fin r)
  have hcommV (z : V ⊗[R] A) : qV (u.lTensor V z) = algebraMap R V (s : R) • EV z := by
    induction z using TensorProduct.inductionOn with
    | tmul k a =>
      ext i
      have hh := congrArg β (hu' a i)
      rw [map_mul, β.commutes, β.commutes] at hh
      change (u a i) • k = algebraMap R V (s : R) * (k * β (ψ a i))
      rw [Algebra.smul_def, hh]
      ring
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hbijV : Function.Bijective (u.lTensor V) := by
    rw [← localizedTensorMap_eq_lTensor (Submonoid.powers g)]
    apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
      (TensorProduct.mk R V A 1) (TensorProduct.mk R V F 1)).mpr
    exact hb' g (dvd_mul_left b d)
  have he : Function.Bijective EV := by
    constructor
    · intro x y hxy
      apply hbijV.1
      apply qV.injective
      rw [hcommV, hcommV, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hbijV.2 (qV.symm (algebraMap R V (s : R) • y))
      refine ⟨z, ?_⟩
      apply hsV.smul_bijective.1
      change algebraMap R V (s : R) • EV z = algebraMap R V (s : R) • y
      rw [← hcommV, hz, qV.apply_symm_apply]
  refine ⟨g, hg, hdg, AlgEquiv.ofBijective EV he, ?_⟩
  intro a i
  change (EV ((1 : V) ⊗ₜ[R] a)) i = β (ψ a i)
  simp only [EV, AlgHom.liftEquiv_tmul, one_smul]
  rfl

end SerrePositivity
