module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DivisibleHomZero
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteIdealExtension
public import SerrePositivity.CommutativeAlgebra.Almost.Zero
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Complete almost extension closure from the actual conormal module I/I²

Scalar surjectivity on the conormal module is a mathematical hypothesis here;
it is not deduced from idempotence of ordinary mod-aⁿ images.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R) (I : Ideal R)

/-- If the actual conormal is a-divisible, square annihilation of a derived-complete
module improves to annihilation by I itself. -/
lemma ideal_annihilates_of_square_annihilates_of_conormal_surjective
    (hI : Function.Surjective (fun x : I.Cotangent => a • x))
    (N : ModuleCat.{u} R) (hN : IsModuleComplete R a N)
    (hsq : I ^ 2 ≤ Module.annihilator R N) : I ≤ Module.annihilator R N := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  let μ : I →ₗ[R] N := (LinearMap.toSpanSingleton R N x).comp I.subtype
  have hk : (I • (⊤ : Submodule R I)) ≤ μ.ker := by
    intro y hy
    have hyk : y ∈ LinearMap.ker I.toCotangent := by
      change I.toCotangent y = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr hy
    have hy₂ := I.mem_toCotangent_ker.mp hyk
    change (y : R) • x = 0
    exact Module.mem_annihilator.mp (hsq hy₂) x
  let q : I.Cotangent →ₗ[R] N := (I • (⊤ : Submodule R I)).liftQ μ hk
  have hq := linearMap_eq_zero_of_smul_surjective_of_isModuleComplete a
    (ModuleCat.of R I.Cotangent) N hI hN q
  exact congrArg (fun f : I.Cotangent →ₗ[R] N => f (I.toCotangent ⟨r, hr⟩)) hq

/-- The actual conormal criterion supplies the complete extension-closure property. -/
lemma completeIdealExtensionClosed_of_conormal_surjective
    (hI : Function.Surjective (fun x : I.Cotangent => a • x)) :
    CompleteIdealExtensionClosed R a I := by
  intro S hS _ h₂ _ h₁ h₃
  have he : Function.Exact S.f.hom S.g.hom := by
    intro x
    constructor
    · exact (ShortComplex.moduleCat_exact_iff S).mp hS.exact x
    · rintro ⟨y, rfl⟩
      exact congrArg (fun f => f.hom y) S.zero
  have hs : I * I ≤ Module.annihilator R S.X₂ :=
    Almost.IsAlmostZero.of_exact_mul S.f.hom S.g.hom
      he h₁ h₃
  apply ideal_annihilates_of_square_annihilates_of_conormal_surjective a I hI S.X₂ h₂
  simpa only [pow_two] using hs

end SerrePositivity.DerivedCompletion
