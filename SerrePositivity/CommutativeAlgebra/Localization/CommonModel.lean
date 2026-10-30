module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Basic
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-! # 同じ局所化をもつ二つの代数の有限な共通模型

## 概要

同じ局所化をもつ二つの代数について、局所化の中の像から有限な共通の中間代数（共通模型）を作り、比較写像の余核が一つの冪で消えることを示す。有限表示の場合の版と、局所化の比較のテンソル写像も与える。

## 方針

共通模型は局所化の中の両方の像が生成する部分代数。前半の共通部分（比較写像と二つの instance）を一度だけ作り、有限生成版と有限表示版で使う。

## 規約

`localizationComparisonTensorEquiv_tmul` は `@[simp]`。

## 使われ方

CLMST の局所的な比較（Prop 2.4.7 の定数階数の場合）、主局所化の同種写像の降下。
-/

@[expose] public noncomputable section

universe u

section FiniteCommonLocalizationModelPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- Two finite algebras mapping into one localized algebra have a finite common
intermediate algebra inside that target, and the target is its module localization. -/
theorem exists_finite_common_localization_model
    {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    [Module.Finite R A] [Module.Finite R B]
    (S : Submonoid R) (f : A →ₐ[R] T) (h : B →ₐ[R] T)
    [IsLocalizedModule S f.toLinearMap] :
    ∃ E : Subalgebra R T, Module.Finite R E ∧
      IsLocalizedModule S E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : B →ₐ[R] E),
        E.val.comp u = f ∧ E.val.comp v = h ∧
          u.toRingHom.Finite ∧ v.toRingHom.Finite := by
  let ψ : A ⊗[R] B →ₐ[R] T :=
    Algebra.TensorProduct.lift f h (fun _ _ => Commute.all _ _)
  let E : Subalgebra R T := ψ.range
  let u : A →ₐ[R] E := ψ.rangeRestrict.comp (Algebra.TensorProduct.includeLeft : A →ₐ[R] _)
  let v : B →ₐ[R] E := ψ.rangeRestrict.comp (Algebra.TensorProduct.includeRight : B →ₐ[R] _)
  have hu : E.val.comp u = f := by
    ext x
    change ψ (x ⊗ₜ[R] (1 : B)) = f x
    simp only [ψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hv : E.val.comp v = h := by
    ext x
    change ψ ((1 : A) ⊗ₜ[R] x) = h x
    simp only [ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hfinite : Module.Finite R E :=
    Module.Finite.of_surjective ψ.rangeRestrict.toLinearMap ψ.rangeRestrict_surjective
  have hloc : IsLocalizedModule S E.val.toLinearMap := by
    constructor
    · exact IsLocalizedModule.map_units (S := S) (f := f.toLinearMap)
    · intro t
      obtain ⟨⟨a, s⟩, ha⟩ := IsLocalizedModule.surj S f.toLinearMap t
      refine ⟨(u a, s), ?_⟩
      change s • t = E.val (u a)
      rw [show E.val (u a) = f a from RingHom.congr_fun (congrArg AlgHom.toRingHom hu) a]
      exact ha
    · intro x y hxy
      refine ⟨1, ?_⟩
      have he : x = y := Subtype.ext hxy
      simpa only [one_smul] using he
  have huF : u.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (u.toRingHom.comp (algebraMap R A)).Finite from by
      change ((u : A →+* E).comp (algebraMap R A)).Finite
      rw [u.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  have hvF : v.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (v.toRingHom.comp (algebraMap R B)).Finite from by
      change ((v : B →+* E).comp (algebraMap R B)).Finite
      rw [v.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  exact ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF⟩

/-- A splitting over any localization gives a finite common model inside the
specified localized algebra, with both original coefficient maps. -/
theorem localizationSplitting_exists_finite_common_model
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ E : Subalgebra R (Fin r → L), Module.Finite R E ∧
      IsLocalizedModule S E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R L (b i)) ∧
          u.toRingHom.Finite ∧ v.toRingHom.Finite := by
  let f : A →ₐ[R] (Fin r → L) := (e.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A)
  let h : (Fin r → R) →ₐ[R] (Fin r → L) :=
    AlgHom.pi (fun i => (Algebra.ofId R L).comp (Pi.evalAlgHom R (fun _ : Fin r => R) i))
  have hf : f.toLinearMap = (e.restrictScalars R).toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk R L A 1) := by
    ext x i
    rfl
  let : IsLocalizedModule S f.toLinearMap := by
    rw [hf]
    exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R L A 1)
      (e.restrictScalars R).toLinearEquiv
  obtain ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF⟩ :=
    exists_finite_common_localization_model S f h
  refine ⟨E, hfinite, hloc, u, v, ?_, ?_, huF, hvF⟩
  · intro a
    exact AlgHom.congr_fun hu a
  · intro b i
    exact congrArg (fun z : Fin r → L => z i) (AlgHom.congr_fun hv b)

end SerrePositivity

end FiniteCommonLocalizationModelPart

section FiniteCommonLocalizationBoundsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- A specified localized splitting yields actual finite comparisons whose two
cokernels share one exponent and whose kernels are power torsion. -/
theorem localizationSplitting_exists_finite_common_model_bounds
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ E : Subalgebra R (Fin r → L), Module.Finite R E ∧
      IsLocalizedModule (.powers d) E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R L (b i)) ∧
        u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
        (∀ a, u a = 0 → ∃ n : ℕ, d ^ n • a = 0) ∧
        (∀ b, v b = 0 → ∃ n : ℕ, d ^ n • b = 0) ∧
        ∃ n : ℕ, (∀ y : E ⧸ u.toLinearMap.range, d ^ n • y = 0) ∧
          (∀ y : E ⧸ v.toLinearMap.range, d ^ n • y = 0) := by
  let f : A →ₐ[R] (Fin r → L) := (e.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A)
  let h : (Fin r → R) →ₐ[R] (Fin r → L) :=
    AlgHom.pi (fun i => (Algebra.ofId R L).comp (Pi.evalAlgHom R (fun _ : Fin r => R) i))
  have hf : f.toLinearMap = (e.restrictScalars R).toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk R L A 1) := by
    ext x i
    rfl
  let : IsLocalizedModule (.powers d) f.toLinearMap := by
    rw [hf]
    exact IsLocalizedModule.of_linearEquiv (.powers d) (TensorProduct.mk R L A 1)
      (e.restrictScalars R).toLinearEquiv
  let q := TensorProduct.piScalarRight R L L (Fin r)
  have hh : h.toLinearMap = (q.restrictScalars R).toLinearMap.comp
      (TensorProduct.mk R L (Fin r → R) 1) := by
    apply LinearMap.ext
    intro x
    apply funext
    intro i
    change algebraMap R L (x i) = (x i) • (1 : L)
    simp only [Algebra.smul_def, mul_one]
  let : IsLocalizedModule (.powers d) h.toLinearMap := by
    rw [hh]
    exact IsLocalizedModule.of_linearEquiv (.powers d)
      (TensorProduct.mk R L (Fin r → R) 1) (q.restrictScalars R)
  obtain ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF⟩ :=
    localizationSplitting_exists_finite_common_model (.powers d) L r e
  let : Module.Finite R E := hfinite
  have hcomp : E.val.toLinearMap.comp u.toLinearMap = f.toLinearMap := by
    ext a i
    exact congrArg (fun z : Fin r → L => z i) (hu a)
  have hcomp' : E.val.toLinearMap.comp v.toLinearMap = h.toLinearMap := by
    apply LinearMap.ext
    intro b
    apply funext
    intro i
    exact hv b i
  have hinj : Function.Injective E.val.toLinearMap := Subtype.val_injective
  refine ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF, ?_, ?_, ?_⟩
  · intro a ha
    exact localizationComparison_ker_power_torsion d u.toLinearMap f.toLinearMap
      E.val.toLinearMap hcomp a ha
  · intro b hb
    exact localizationComparison_ker_power_torsion d v.toLinearMap h.toLinearMap
      E.val.toLinearMap hcomp' b hb
  · exact localizationComparisons_exists_common_pow_annihilates_cokers d
      u.toLinearMap v.toLinearMap f.toLinearMap h.toLinearMap E.val.toLinearMap hinj hcomp hcomp'

end SerrePositivity

end FiniteCommonLocalizationBoundsPart

section FinitePresentationCommonLocalizationModelPart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- A comparison with power-torsion cokernel transfers a localization structure
to its target. No injectivity or finite presentation is needed. -/
theorem isLocalizedModule_of_comparison_power_torsion_coker
    {R M N X : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup X] [Module R X]
    (d : R) (f : M →ₗ[R] N) (l : M →ₗ[R] X) (v : N →ₗ[R] X)
    [IsLocalizedModule (.powers d) l] (hcomp : v.comp f = l)
    (hcoker : ∀ y : N, ∃ n : ℕ, d ^ n • y ∈ f.range) :
    IsLocalizedModule (.powers d) v := by
  constructor
  · exact IsLocalizedModule.map_units (S := .powers d) (f := l)
  · intro z
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (.powers d) l z
    refine ⟨(f x, s), ?_⟩
    change s • z = v (f x)
    rw [show v (f x) = l x from LinearMap.congr_fun hcomp x]
    exact hs
  · intro y y' hyy
    obtain ⟨n, x, hx⟩ := hcoker (y - y')
    have hlx : l x = 0 := by
      rw [← hcomp, LinearMap.comp_apply, hx, map_smul, map_sub, hyy, sub_self, smul_zero]
    obtain ⟨m, hm⟩ := localizationComparison_ker_power_torsion d
      l l (LinearMap.id : X →ₗ[R] X) (by rfl) x hlx
    refine ⟨⟨d ^ (m + n), ⟨m + n, rfl⟩⟩, ?_⟩
    change d ^ (m + n) • y = d ^ (m + n) • y'
    apply sub_eq_zero.mp
    rw [← smul_sub, pow_add, mul_smul, ← hx, ← map_smul, hm, map_zero]

/-- Two finite, finitely presented algebras over R have a common finite,
finitely presented model whenever the first map is a localization. The map
from the model to the localized target is retained and need not be injective. -/
theorem exists_finitePresentation_common_localization_model
    {R A B X : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing X]
    [Algebra R A] [Algebra R B] [Algebra R X]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
    (d : R) (f : A →ₐ[R] X) (h : B →ₐ[R] X)
    [IsLocalizedModule (.powers d) f.toLinearMap] :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Algebra.FinitePresentation R E ∧ Module.FinitePresentation R E ∧
      ∃ (u : A →ₐ[R] E) (v : B →ₐ[R] E) (w : E →ₐ[R] X),
        w.comp u = f ∧ w.comp v = h ∧
        IsLocalizedModule (.powers d) w.toLinearMap := by
  classical
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := R) (M := B)
  have hden : ∀ i : Fin m, ∃ n : ℕ, ∃ a : A, d ^ n • h (b i) = f a := by
    intro i
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (.powers d) f.toLinearMap (h (b i))
    obtain ⟨n, hn⟩ := s.2
    change d ^ n = (s : R) at hn
    change (s : R) • h (b i) = f a at hs
    exact ⟨n, a, by simpa only [hn] using hs⟩
  choose k a ha using hden
  let n := ∑ i, k i
  let a' : Fin m → A := fun i => d ^ (n - k i) • a i
  have hclear (i : Fin m) : d ^ n • h (b i) = f (a' i) := by
    have hi : k i ≤ n := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [show n = (n - k i) + k i from (Nat.sub_add_cancel hi).symm, pow_add, mul_smul, ha]
    exact (f.toLinearMap.map_smul _ _).symm
  let P := A ⊗[R] B
  let ψ : P →ₐ[R] X := Algebra.TensorProduct.lift f h (fun _ _ => Commute.all _ _)
  let rel : Fin m → P := fun i => d ^ n • ((1 : A) ⊗ₜ[R] b i) - (a' i ⊗ₜ[R] (1 : B))
  let J : Ideal P := Ideal.span (Set.range rel)
  have hJ : J ≤ RingHom.ker ψ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ψ (rel i) = 0
    change ψ (d ^ n • (1 ⊗ₜ[R] b i) - (a' i ⊗ₜ[R] 1)) = 0
    rw [map_sub]
    change ψ.toLinearMap (d ^ n • (1 ⊗ₜ[R] b i)) - ψ (a' i ⊗ₜ[R] 1) = 0
    rw [LinearMap.map_smul]
    change d ^ n • (f 1 * h (b i)) - (f (a' i) * h 1) = 0
    simpa only [map_one, one_mul, mul_one, sub_eq_zero] using hclear i
  let E := P ⧸ J
  let q : P →ₐ[R] E := Ideal.Quotient.mkₐ R J
  let u : A →ₐ[R] E := q.comp Algebra.TensorProduct.includeLeft
  let v : B →ₐ[R] E := q.comp Algebra.TensorProduct.includeRight
  let w : E →ₐ[R] X := Ideal.Quotient.liftₐ J ψ (fun z hz => hJ hz)
  have hu : w.comp u = f := by
    ext x
    change f x * h 1 = f x
    rw [map_one, mul_one]
  have hv : w.comp v = h := by
    ext x
    change f 1 * h x = h x
    rw [map_one, one_mul]
  have hrel (i : Fin m) : d ^ n • v (b i) = u (a' i) := by
    have hz : q (rel i) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_range_self i))
    change q (d ^ n • (1 ⊗ₜ[R] b i) - (a' i ⊗ₜ[R] 1)) = 0 at hz
    change d ^ n • q (1 ⊗ₜ[R] b i) = q (a' i ⊗ₜ[R] 1)
    simpa only [map_sub, map_smul, sub_eq_zero] using hz
  have hb' (z : B) : d ^ n • v z ∈ u.toLinearMap.range := by
    let F : B →ₗ[R] E := d ^ n • v.toLinearMap
    have H : Submodule.span R (Set.range b) ≤ u.toLinearMap.range.comap F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨a' i, (hrel i).symm⟩
    rw [hb] at H
    exact H Submodule.mem_top
  have hq (z : P) : d ^ n • q z ∈ u.toLinearMap.range := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨a, ha⟩ := hb' y
      change u a = d ^ n • v y at ha
      refine ⟨x * a, ?_⟩
      change u (x * a) = d ^ n • q (x ⊗ₜ[R] y)
      rw [map_mul, ha, mul_smul_comm]
      congr 1
      change q (x ⊗ₜ[R] 1) * q (1 ⊗ₜ[R] y) = q (x ⊗ₜ[R] y)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
      simpa only [map_add, smul_add] using u.toLinearMap.range.add_mem hx hy
  have hcoker (z : E) : ∃ n : ℕ, d ^ n • z ∈ u.toLinearMap.range := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J z
    exact ⟨n, hq z⟩
  have hloc : IsLocalizedModule (.powers d) w.toLinearMap :=
    isLocalizedModule_of_comparison_power_torsion_coker d u.toLinearMap f.toLinearMap
      w.toLinearMap (congrArg AlgHom.toLinearMap hu) hcoker
  have hfg : J.FG := Submodule.fg_span (Set.finite_range rel)
  let : Algebra.FinitePresentation R P := Algebra.FinitePresentation.trans R A P
  let : Algebra.FinitePresentation R E := Algebra.FinitePresentation.quotient hfg
  let : Module.Finite R E := Module.Finite.of_surjective q.toLinearMap
    (Ideal.Quotient.mkₐ_surjective R J)
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.FinitePresentation.of_finite_of_finitePresentation R E, u, v, w, hu, hv, hloc⟩

end SerrePositivity

end FinitePresentationCommonLocalizationModelPart

section FinitePresentationCommonLocalizationBoundsPart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- A localized splitting gives a finite, finitely presented common model with
both original maps, their support bounds and one common cokernel exponent. -/
theorem localizationSplitting_exists_finitePresentation_common_model_bounds
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Algebra.FinitePresentation R E ∧ Module.FinitePresentation R E ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E) (w : E →ₐ[R] (Fin r → L)),
        (∀ a, w (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, w (v b) i = algebraMap R L (b i)) ∧
        IsLocalizedModule (.powers d) w.toLinearMap ∧
        u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
        (∀ a, u a = 0 → ∃ n : ℕ, d ^ n • a = 0) ∧
        (∀ b, v b = 0 → ∃ n : ℕ, d ^ n • b = 0) ∧
        ∃ n : ℕ, (∀ y : E ⧸ u.toLinearMap.range, d ^ n • y = 0) ∧
          (∀ y : E ⧸ v.toLinearMap.range, d ^ n • y = 0) := by
  let f : A →ₐ[R] (Fin r → L) := (e.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A)
  let h : (Fin r → R) →ₐ[R] (Fin r → L) :=
    AlgHom.pi (fun i => (Algebra.ofId R L).comp (Pi.evalAlgHom R (fun _ : Fin r => R) i))
  have hf : f.toLinearMap = (e.restrictScalars R).toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk R L A 1) := by ext x i; rfl
  let : IsLocalizedModule (.powers d) f.toLinearMap := by
    rw [hf]
    exact IsLocalizedModule.of_linearEquiv (.powers d) (TensorProduct.mk R L A 1)
      (e.restrictScalars R).toLinearEquiv
  let q := TensorProduct.piScalarRight R L L (Fin r)
  have hh : h.toLinearMap = (q.restrictScalars R).toLinearMap.comp
      (TensorProduct.mk R L (Fin r → R) 1) := by
    apply LinearMap.ext
    intro x
    apply funext
    intro i
    change algebraMap R L (x i) = (x i) • (1 : L)
    simp only [Algebra.smul_def, mul_one]
  let : IsLocalizedModule (.powers d) h.toLinearMap := by
    rw [hh]
    exact IsLocalizedModule.of_linearEquiv (.powers d)
      (TensorProduct.mk R L (Fin r → R) 1) (q.restrictScalars R)
  obtain ⟨E, hE, aE, hfinite, hfp, hmfp, u, v, w, hu, hv, hloc⟩ :=
    exists_finitePresentation_common_localization_model d f h
  let : Module.Finite R E := hfinite
  let : IsLocalizedModule (.powers d) w.toLinearMap := hloc
  have huF : u.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (u.toRingHom.comp (algebraMap R A)).Finite from by
      change ((u : A →+* E).comp (algebraMap R A)).Finite
      rw [u.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  have hvF : v.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (v.toRingHom.comp (algebraMap R (Fin r → R))).Finite from by
      change ((v : (Fin r → R) →+* E).comp (algebraMap R (Fin r → R))).Finite
      rw [v.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  have hu' : w.toLinearMap.comp u.toLinearMap = f.toLinearMap :=
    congrArg AlgHom.toLinearMap hu
  have hv' : w.toLinearMap.comp v.toLinearMap = h.toLinearMap :=
    congrArg AlgHom.toLinearMap hv
  refine ⟨E, hE, aE, hfinite, hfp, hmfp, u, v, w, ?_, ?_, hloc, huF, hvF, ?_, ?_, ?_⟩
  · intro a
    exact AlgHom.congr_fun hu a
  · intro b i
    exact congrArg (fun z : Fin r → L => z i) (AlgHom.congr_fun hv b)
  · exact fun a ha => localizationComparison_ker_power_torsion d
      u.toLinearMap f.toLinearMap w.toLinearMap hu' a ha
  · exact fun b hb => localizationComparison_ker_power_torsion d
      v.toLinearMap h.toLinearMap w.toLinearMap hv' b hb
  · exact localizationComparisons_exists_common_pow_annihilates_cokers_of_localized_target d
      u.toLinearMap v.toLinearMap f.toLinearMap h.toLinearMap w.toLinearMap hu' hv'

end SerrePositivity

end FinitePresentationCommonLocalizationBoundsPart

section LocalizationComparisonTensorEquivPart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The canonical multiplication map from the base change of a specified
localization is an algebra isomorphism. -/
def localizationComparisonTensorEquiv
    {R A X : Type u} [CommRing R] [CommRing A] [CommRing X]
    [Algebra R A] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] X) [IsLocalizedModule S f.toLinearMap] :
    L ⊗[R] A ≃ₐ[L] X := by
  let g : L ⊗[R] A →ₐ[L] X :=
    Algebra.TensorProduct.lift (Algebra.ofId L X) f (fun _ _ => Commute.all _ _)
  let j : A →ₗ[R] L ⊗[R] A := TensorProduct.mk R L A 1
  have hcomp : (g.restrictScalars R).toLinearMap.comp j = f.toLinearMap := by
    ext a
    change algebraMap L X 1 * f a = f a
    rw [map_one, one_mul]
  let : IsLocalizedModule S ((g.restrictScalars R).toLinearMap.comp j) := by
    rw [hcomp]
    infer_instance
  have he := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S j
    (g.restrictScalars R).toLinearMap
  have hbij : Function.Bijective g := by
    change Function.Bijective (g.restrictScalars R).toLinearMap
    rw [← he]
    exact (IsLocalizedModule.linearEquiv S j
      ((g.restrictScalars R).toLinearMap.comp j)).bijective
  exact AlgEquiv.ofBijective g hbij

/-- The isomorphism evaluates at the original tensor generators by the original map. -/
theorem localizationComparisonTensorEquiv_tmul
    {R A X : Type u} [CommRing R] [CommRing A] [CommRing X]
    [Algebra R A] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] X) [IsLocalizedModule S f.toLinearMap] (l : L) (a : A) :
    localizationComparisonTensorEquiv S L f (l ⊗ₜ[R] a) = algebraMap L X l * f a := rfl

/-- The tensor isomorphisms commute with the actual coefficient extension. -/
theorem localizationComparisonTensorEquiv_comp_tensorMap
    {R A B X : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing X]
    [Algebra R A] [Algebra R B] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] B) (w : B →ₐ[R] X)
    [IsLocalizedModule S w.toLinearMap] [IsLocalizedModule S (w.comp f).toLinearMap] :
    (localizationComparisonTensorEquiv S L w).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id L L) f) =
      (localizationComparisonTensorEquiv S L (w.comp f)).toAlgHom := by
  ext a
  change algebraMap L X 1 * w (f a) = algebraMap L X 1 * w (f a)
  rfl

/-- If a comparison and its target have the same actual localization, the
original algebra map becomes bijective on tensoring with the localization. -/
theorem localizationComparison_tensorMap_bijective
    {R A B X : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing X]
    [Algebra R A] [Algebra R B] [Algebra R X]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    [Algebra L X] [IsScalarTower R L X]
    (f : A →ₐ[R] B) (w : B →ₐ[R] X)
    [IsLocalizedModule S w.toLinearMap] [IsLocalizedModule S (w.comp f).toLinearMap] :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) f) := by
  let e := localizationComparisonTensorEquiv S L w
  let e' := localizationComparisonTensorEquiv S L (w.comp f)
  have hcomp : e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id L L) f) =
      e'.toAlgHom := localizationComparisonTensorEquiv_comp_tensorMap S L f w
  have hbij : Function.Bijective
      (e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id L L) f)) := by
    rw [hcomp]
    exact e'.bijective
  constructor
  · intro x y hxy
    exact hbij.injective (congrArg e hxy)
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective (e y)
    exact ⟨x, e.injective hx⟩

/-- The two maps supplied by a localized splitting become bijective after
base change, for the same E,u,v,w as in the finite presentation construction. -/
theorem localizationSplitting_common_model_tensorMaps_bijective
    {R A E : Type u} [CommRing R] [CommRing A] [CommRing E]
    [Algebra R A] [Algebra R E]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E) (w : E →ₐ[R] (Fin r → L))
    [IsLocalizedModule S w.toLinearMap]
    (hu : ∀ a, w (u a) = e ((1 : L) ⊗ₜ[R] a))
    (hv : ∀ b i, w (v b) i = algebraMap R L (b i)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) u) ∧
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L) v) := by
  have hu' : (w.comp u).toLinearMap = (e.restrictScalars R).toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk R L A 1) := by
    apply LinearMap.ext
    intro a
    exact hu a
  let : IsLocalizedModule S (w.comp u).toLinearMap := by
    rw [hu']
    exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R L A 1)
      (e.restrictScalars R).toLinearEquiv
  let q := TensorProduct.piScalarRight R L L (Fin r)
  have hv' : (w.comp v).toLinearMap = (q.restrictScalars R).toLinearMap.comp
      (TensorProduct.mk R L (Fin r → R) 1) := by
    apply LinearMap.ext
    intro b
    apply funext
    intro i
    change w (v b) i = (b i) • (1 : L)
    rw [hv]
    simp only [Algebra.smul_def, mul_one]
  let : IsLocalizedModule S (w.comp v).toLinearMap := by
    rw [hv']
    exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R L (Fin r → R) 1)
      (q.restrictScalars R)
  exact ⟨localizationComparison_tensorMap_bijective S L u w,
    localizationComparison_tensorMap_bijective S L v w⟩

/-- Original R-power support bounds imply that the actual canonical map of
principal ring localizations is bijective. Neither original map is assumed
injective or surjective. -/
theorem localizationComparison_awayMap_bijective_of_power_bounds
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (d : R) (f : A →ₐ[R] B)
    (hker : ∀ a, f a = 0 → ∃ n : ℕ, d ^ n • a = 0)
    (hcoker : ∀ b : B, ∃ n : ℕ, d ^ n • b ∈ f.toLinearMap.range) :
    Function.Bijective (IsLocalization.Away.map
      (Localization.Away (algebraMap R A d))
      (Localization.Away (f (algebraMap R A d))) f.toRingHom (algebraMap R A d)) := by
  constructor
  · apply (IsLocalization.Away.map_injective_iff _ _ _).mpr
    intro a ha
    obtain ⟨n, hn⟩ := hker a ha
    exact ⟨n, by simpa only [Algebra.smul_def, map_pow] using hn⟩
  · apply (IsLocalization.Away.map_surjective_iff _ _ _ _).mpr
    intro b
    obtain ⟨n, a, ha⟩ := hcoker b
    change f a = d ^ n • b at ha
    refine ⟨a, n, ?_⟩
    change f a = f (algebraMap R A d) ^ n * b
    rw [f.commutes]
    simpa only [Algebra.smul_def, map_pow] using ha

/-- The canonical principal localization map, packaged as an R-algebra
isomorphism with the original map on the source ring. -/
def localizationComparisonAwayEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (d : R) (f : A →ₐ[R] B)
    (hker : ∀ a, f a = 0 → ∃ n : ℕ, d ^ n • a = 0)
    (hcoker : ∀ b : B, ∃ n : ℕ, d ^ n • b ∈ f.toLinearMap.range) :
    Localization.Away (algebraMap R A d) ≃ₐ[R]
      Localization.Away (f (algebraMap R A d)) :=
  AlgEquiv.ofBijective (IsLocalization.Away.mapₐ _ _ f (algebraMap R A d))
    (localizationComparison_awayMap_bijective_of_power_bounds d f hker hcoker)

/-- The principal localization isomorphism extends the specified original map. -/
theorem localizationComparisonAwayEquiv_algebraMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (d : R) (f : A →ₐ[R] B)
    (hker : ∀ a, f a = 0 → ∃ n : ℕ, d ^ n • a = 0)
    (hcoker : ∀ b : B, ∃ n : ℕ, d ^ n • b ∈ f.toLinearMap.range) (a : A) :
    localizationComparisonAwayEquiv d f hker hcoker
        (algebraMap A (Localization.Away (algebraMap R A d)) a) =
      algebraMap B (Localization.Away (f (algebraMap R A d))) (f a) := by
  change IsLocalization.Away.map _ _ f.toRingHom _ (algebraMap A _ a) = _
  exact IsLocalization.map_eq _ a

end SerrePositivity

end LocalizationComparisonTensorEquivPart
