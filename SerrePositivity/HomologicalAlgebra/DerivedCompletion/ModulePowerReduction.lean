module

public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Ordinary power reductions of arbitrary modules and their standard maps -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)

/-- The ordinary quotient M/aⁿM, with its original restricted R-action. -/
abbrev modulePowerReduction (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (AdicReduction (Ideal.span {a ^ n}) M)

/-- The original ordinary quotient map. -/
def modulePowerReductionMap (n : ℕ) : M ⟶ modulePowerReduction a M n :=
  ModuleCat.ofHom (Ideal.span {a ^ n} • (⊤ : Submodule R M)).mkQ

instance modulePowerReductionMap_epi (n : ℕ) : Epi (modulePowerReductionMap a M n) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- The reduction is killed by the specified power, without any torsion condition on M. -/
lemma modulePowerReduction_pow_smul_zero (n : ℕ) (x : modulePowerReduction a M n) :
    a ^ n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (Ideal.span {a ^ n} • (⊤ : Submodule R M)).mkQ (a ^ n • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top

lemma modulePowerReductionMap_zero (n : ℕ) :
    (a ^ n • 𝟙 M) ≫ modulePowerReductionMap a M n = 0 := by
  ext x
  exact modulePowerReduction_pow_smul_zero a M n (modulePowerReductionMap a M n x)

/-- Scalar multiplication followed by the original quotient is an exact sequence. -/
abbrev modulePowerReductionShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (a ^ n • 𝟙 M) (modulePowerReductionMap a M n)
    (modulePowerReductionMap_zero a M n)

lemma modulePowerReductionShortComplex_exact (n : ℕ) :
    (modulePowerReductionShortComplex a M n).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : x ∈ Ideal.span {a ^ n} • (⊤ : Submodule R M) :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y, hy⟩ := (mem_principal_pow_smul_top a n x).mp
    (by simpa only [Ideal.span_singleton_pow] using hx')
  exact ⟨y, hy⟩

/-- The ordinary reduction transition is induced by the identity of M. -/
def modulePowerReductionTransition (n : ℕ) :
    modulePowerReduction a M (n + 1) ⟶ modulePowerReduction a M n :=
  ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_principal_pow_smul_top a (n + 1) x).mp
      (by simpa only [Ideal.span_singleton_pow] using hx)
    change x ∈ Ideal.span {a ^ n} • (⊤ : Submodule R M)
    rw [← hy]
    have he : a ^ (n + 1) • y = a ^ n • (a • y) := by rw [pow_succ, mul_smul]
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _))
      Submodule.mem_top))

@[reassoc] lemma modulePowerReductionTransition_π (n : ℕ) :
    modulePowerReductionMap a M (n + 1) ≫ modulePowerReductionTransition a M n =
      modulePowerReductionMap a M n := by
  ext x
  rfl

instance modulePowerReductionTransition_epi (n : ℕ) :
    Epi (modulePowerReductionTransition a M n) :=
  epi_of_epi_fac (modulePowerReductionTransition_π a M n)

end SerrePositivity.DerivedCompletion
