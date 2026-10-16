module
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Tactic.LinearCombination

/-! # Descending an actual finite algebra map from a localization to a principal neighborhood -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- A map from a finitely presented finite module algebra to a localization descends
to a principal neighborhood, preserving multiplication, the unit, and its original map. -/
theorem finiteAlgebra_exists_away_lift
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
    (φ : A →ₐ[R] S) :
    ∃ (d : R) (hd : d ∈ M) (ψ : A →ₐ[R] Localization.Away d),
      (IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R S)
        (IsLocalization.map_units S ⟨d, hd⟩)).comp ψ = φ := by
  classical
  let f : R →ₗ[R] S := Algebra.linearMap R S
  obtain ⟨u, s, hu⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule M f φ.toLinearMap
  have hu' (a : A) : algebraMap R S (u a) = algebraMap R S (s : R) * φ a := by
    have ha := LinearMap.congr_fun hu a
    change algebraMap R S (u a) = (s : R) • φ a at ha
    simpa only [Algebra.smul_def] using ha
  let δ : A ⊗[R] A →ₗ[R] R := TensorProduct.lift
    ((s : R) • (LinearMap.mul R A).compr₂ u - (LinearMap.mul R R).compl₁₂ u u)
  have hδapply (a b : A) : δ (a ⊗ₜ[R] b) = (s : R) * u (a * b) - u a * u b := by
    simp only [δ, TensorProduct.lift.tmul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, smul_eq_mul]
    rfl
  have hδ : f.comp δ = f.comp (0 : A ⊗[R] A →ₗ[R] R) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hδapply, map_zero]
    change algebraMap R S ((s : R) * u (a * b) - u a * u b) = 0
    simp only [map_sub, map_mul, hu']
    ring
  obtain ⟨t, ht⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule M f δ 0 hδ
  have ht' (a b : A) : (t : R) * ((s : R) * u (a * b) - u a * u b) = 0 := by
    have hh := LinearMap.congr_fun ht (a ⊗ₜ[R] b)
    simpa only [LinearMap.smul_apply, LinearMap.zero_apply, smul_zero,
      Submonoid.smul_def, smul_eq_mul, hδapply] using hh
  have hone : f (u 1 - (s : R)) = f 0 := by
    change algebraMap R S (u 1 - (s : R)) = algebraMap R S 0
    rw [map_sub, hu', map_one, mul_one, sub_self, map_zero]
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := M) (f := f) hone
  change (v : R) * (u 1 - (s : R)) = (v : R) * 0 at hv
  let d : R := s * t * v
  have hd : d ∈ M := mul_mem (mul_mem s.2 t.2) v.2
  let L := Localization.Away d
  have hdunit : IsUnit (algebraMap R L d) := IsLocalization.Away.algebraMap_isUnit d
  have hsunit : IsUnit (algebraMap R L (s : R)) := isUnit_of_dvd_unit
    (map_dvd (algebraMap R L) ⟨(t : R) * v, by simp [d, mul_assoc]⟩) hdunit
  have htunit : IsUnit (algebraMap R L (t : R)) := isUnit_of_dvd_unit
    (map_dvd (algebraMap R L) ⟨(s : R) * v, by dsimp [d]; ring⟩) hdunit
  have hvunit : IsUnit (algebraMap R L (v : R)) := isUnit_of_dvd_unit
    (map_dvd (algebraMap R L) ⟨(s : R) * t, by dsimp [d]; ring⟩) hdunit
  have hmul (a b : A) : algebraMap R L (s : R) * algebraMap R L (u (a * b)) =
      algebraMap R L (u a) * algebraMap R L (u b) := by
    apply sub_eq_zero.mp
    apply htunit.mul_right_eq_zero.mp
    have hh := congrArg (algebraMap R L) (ht' a b)
    simpa only [map_mul, map_sub, map_zero] using hh
  have hunit : algebraMap R L (u 1) = algebraMap R L (s : R) := by
    apply sub_eq_zero.mp
    apply hvunit.mul_right_eq_zero.mp
    have hh := congrArg (algebraMap R L) hv
    simpa only [smul_eq_mul, mul_zero, map_mul, map_sub, map_zero] using hh
  let w : L := ↑hsunit.unit⁻¹
  have hw : w * algebraMap R L (s : R) = 1 := hsunit.val_inv_mul
  let ψlin : A →ₗ[R] L := w • (Algebra.linearMap R L).comp u
  have ψone : ψlin 1 = 1 := by
    change w * algebraMap R L (u 1) = 1
    rw [hunit]
    exact hw
  have ψmul (a b : A) : ψlin (a * b) = ψlin a * ψlin b := by
    change w * algebraMap R L (u (a * b)) =
      (w * algebraMap R L (u a)) * (w * algebraMap R L (u b))
    linear_combination w ^ 2 * hmul a b - w * algebraMap R L (u (a * b)) * hw
  let ψ : A →ₐ[R] L := AlgHom.ofLinearMap ψlin ψone ψmul
  let α : L →ₐ[R] S := IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R S)
    (IsLocalization.map_units S ⟨d, hd⟩)
  have hα (r : R) : α (algebraMap R L r) = algebraMap R S r := α.commutes r
  have hinv : α w * algebraMap R S (s : R) = 1 := by
    rw [← hα, ← map_mul, hw, map_one]
  refine ⟨d, hd, ψ, ?_⟩
  apply AlgHom.ext
  intro a
  change α (w * algebraMap R L (u a)) = φ a
  rw [map_mul, hα, hu', ← mul_assoc, hinv, one_mul]

/-- All coordinates of a finite product descend to one common principal neighborhood. -/
theorem finiteAlgebra_exists_away_lift_pi
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
    (r : ℕ) (φ : A →ₐ[R] (Fin r → S)) :
    ∃ (d : R) (hd : d ∈ M) (ψ : A →ₐ[R] (Fin r → Localization.Away d)),
      ∀ a i, IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R S)
        (IsLocalization.map_units S ⟨d, hd⟩) (ψ a i) = φ a i := by
  classical
  have hi (i : Fin r) := finiteAlgebra_exists_away_lift M S
    ((Pi.evalAlgHom R (fun _ : Fin r => S) i).comp φ)
  choose d hd ψ hψ using hi
  let D : M := ∏ i : Fin r, (⟨d i, hd i⟩ : M)
  let L := Localization.Away (D : R)
  have hdiv (i : Fin r) : d i ∣ (D : R) := by
    simpa only [D, Submonoid.coe_finsetProd] using
      (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
  have hunit (i : Fin r) : IsUnit (algebraMap R L (d i)) := isUnit_of_dvd_unit
    (map_dvd (algebraMap R L) (hdiv i)) (IsLocalization.Away.algebraMap_isUnit (D : R))
  let β (i : Fin r) : Localization.Away (d i) →ₐ[R] L :=
    IsLocalization.Away.liftAlgHom (d i) (f := Algebra.ofId R L) (hunit i)
  let α : L →ₐ[R] S := IsLocalization.Away.liftAlgHom (D : R) (f := Algebra.ofId R S)
    (IsLocalization.map_units S D)
  have hcomp (i : Fin r) : α.comp (β i) =
      IsLocalization.Away.liftAlgHom (d i) (f := Algebra.ofId R S)
        (IsLocalization.map_units S ⟨d i, hd i⟩) :=
    Subsingleton.elim (h := IsLocalization.algHom_subsingleton (.powers (d i))) _ _
  refine ⟨D, D.2, AlgHom.pi (fun i => (β i).comp (ψ i)), ?_⟩
  intro a i
  change α (β i (ψ i a)) = φ a i
  have hc := AlgHom.congr_fun (hcomp i) (ψ i a)
  exact hc.trans (AlgHom.congr_fun (hψ i) a)

end SerrePositivity
