module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionPure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTowerLimitBound
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic

/-! # G9: complete flat reduction implies purity and bounded power torsion -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))

/-- The actual ordinary power-reduction H0 is killed by that power. -/
lemma powerCokernelH0_power_annihilated (n : ℕ)
    (z : (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology 0) :
    a ^ n • z = 0 := by
  let e := (derivedPowerCokernelHomologyIso a n X 0).toLinearEquiv
  apply e.injective
  rw [map_smul, map_zero]
  change Ideal.Quotient.mk (Ideal.span {a ^ n}) (a ^ n) • e z = 0
  rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), zero_smul]

variable
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
include hPure hFlat

/-- Transfer the flat quotient relation through the actual R-linear homology comparison. -/
lemma powerCokernelH0_torsion_relation (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) (j m : ℕ)
    (z : (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex (j + m)).homology 0)
    (hz : a ^ m • z = 0) :
    ∃ y : (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex (j + m)).homology 0,
      a ^ N • z = a ^ j • y := by
  let q := Ideal.Quotient.mk (Ideal.span {a ^ (j + m)})
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ (j + m)})) 0).obj
    ((boundedAboveDerivedBaseChange q).obj X).obj
  let e := (derivedPowerCokernelHomologyIso a (j + m) X 0).toLinearEquiv
  have hF : Module.Flat (R ⧸ Ideal.span {a ^ (j + m)}) H :=
    (derived_power_reduction_pure_flat a X hPure hFlat (j + m)).2.2
  let := hF
  have hzm : q a ^ m • (e z : H) = 0 := by
    have hez := congrArg e hz
    rw [map_smul, map_zero] at hez
    change q (a ^ m) • (e z : H) = 0 at hez
    simpa only [map_pow] using hez
  obtain ⟨y, hy⟩ := flat_powerQuotient_torsion_relation a N h j m H (e z) hzm
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
  change q (a ^ N) • (e z : H) = q (a ^ j) • y
  simpa only [map_pow] using hy

/-- G9 in the full requested generality, strengthened from natural primes to
arbitrary principal elements. The bound on H0 can be the original ring bound. -/
theorem derived_pure_bounded_torsion_of_complete_flat_reduction
    (hR : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a X.obj) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ n : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj,
          a ^ n • z = 0 → a ^ N • z = 0 := by
  obtain ⟨hGE, hLE⟩ := derived_pure_of_complete_flat_reduction a X hPure hFlat hR hc
  obtain ⟨N, hN⟩ := hR
  let P := (boundedAboveDerivedChosenModel X).complex
  let M : ℕ → Type u := fun n ↦ (powerCokernelComplex a P n).homology 0
  let t := fun n ↦ (homologyMap (powerCokernelComplexTransition a P n) 0).hom
  have hLim := moduleTowerLimit_power_torsion_bound_of_relations a N M t
    (powerCokernelH0_power_annihilated a X)
    (powerCokernelH0_torsion_relation a X hPure hFlat N hN)
  let e := (completeFlatReductionH0LimitIso a X hPure hFlat ⟨N, hN⟩ hc).toLinearEquiv
  refine ⟨hGE, hLE, N, ?_⟩
  intro n z hz
  apply e.injective
  rw [map_smul, map_zero]
  apply hLim n (e z)
  rw [← map_smul, hz, map_zero]

end SerrePositivity.DerivedCompletion
