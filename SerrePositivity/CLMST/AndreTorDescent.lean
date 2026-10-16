module
public import SerrePositivity.BhattScholze.Inputs.AndreFlatness
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatEquiv
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.TorCoefficientPowerTorsionDescent

/-! # The existing André extension detects original power-torsion Tor coefficient actions

This application retains precisely the existing BS Theorem 7.14 input. It does
not assert the absolute-integral-closure splitting or a perfectoid base-change comparison.
-/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

/-- Choose the actual André extension once for the base ring, independently of every Tor test.
Only the existing BS Theorem 7.14 citation is used to supply this extension. -/
lemma exists_andre_extension_detects_powerTorsion_Tor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧
      (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C]
        (N : ModuleCat.{u} R) (k : ℕ) (_hN : ∀ x : N, (p : R) ^ k • x = 0)
        (i : ℕ) (s : R),
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
          ∀ x : (DerivedCategory.homologyFunctor (ModuleCat E) (-(i : ℤ))).obj
            ((boundedAboveDerivedBaseChange (algebraMap R E)).obj
              (boundedAboveDerivedTensor.obj
                (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C),
                  boundedAboveDerivedSingleFunctor.obj N))).obj,
            algebraMap R E s • x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic⟩ :=
    BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  letI := hEring
  letI := hEalg
  let e : baseChangeScalarModule (algebraMap R E) ≅ ModuleCat.of R E :=
    algebraSelfRestrictionIso R E
  have hφ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)}) e.toLinearEquiv.symm hflat
  have hroots : ∀ s : E, ∃ ρ : ℕ → E,
      ρ 0 = s ∧ ∀ n, ρ (n + 1) ^ p = ρ n :=
    fun s => haic.exists_compatible_pow_roots (Fact.out : p.Prime).pos s
  choose ρ hρ0 hρ using hroots
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro C _ _ N k hN i s
  exact torCoefficientScalar_eq_zero_iff_powerTorsion_baseChange
    (algebraMap R E) (p : R) hφ N k hN i s

end SerrePositivity.CLMST
