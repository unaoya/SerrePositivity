module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # 局所化への有限代数の写像の主局所化への降下

## 概要

有限表示な代数から局所化への写像は、ある主局所化 R[1/g] からの写像まで下ろせる（`finiteAlgebra_exists_away_lift`）。茎で指定した有限積と一致する代数の比較は、より小さな主近傍で実際の代数同型にできる。

## 方針

有限表示の生成元と関係式の分母を一つにまとめる。同型への縮小では、局所化した加群の写像を係数拡大の `lTensor` と同一視して、核と余核を消す主元を選ぶ。

## 規約

提出候補（価値が高い）。

## 使われ方

CLMST の局所的な分解、KTheory の局所化、AbsolutelyIntegrallyClosed/Etale の主開集合での分解。
-/

@[expose] public noncomputable section

universe u

section FiniteAlgebraLocalizationLiftPart

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

end FiniteAlgebraLocalizationLiftPart

section PrincipalAlgebraIsomorphismLocusPart

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

end PrincipalAlgebraIsomorphismLocusPart
