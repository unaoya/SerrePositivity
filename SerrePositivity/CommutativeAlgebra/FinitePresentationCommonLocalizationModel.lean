module

public import SerrePositivity.CommutativeAlgebra.FiniteCommonLocalizationModel
public import SerrePositivity.CommutativeAlgebra.LocalizationComparisonBounds
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Finite presentation common models for localized comparisons

A finite set of denominator-clearing relations gives a quotient of the tensor
product. Unlike its image in the localization, this quotient retains finite
presentation over a non-Noetherian base.
-/

@[expose] public noncomputable section
universe u
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
