module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # No maps from an a-divisible module to a derived-a-complete module -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R)

/-- The recurrence injectivity criterion forbids nonzero maps from an a-divisible
module. No separation or bounded torsion hypothesis is imposed. -/
lemma linearMap_eq_zero_of_smul_surjective_of_isModuleComplete
    (M N : ModuleCat.{u} R) (hM : Function.Surjective (fun x : M => a • x))
    (hN : IsModuleComplete R a N) (f : M →ₗ[R] N) : f = 0 := by
  classical
  apply LinearMap.ext
  intro m
  let x : ℕ → M := fun n => Nat.rec m (fun _ z => Classical.choose (hM z)) n
  have hx : ∀ n, a • x (n + 1) = x n := fun n => Classical.choose_spec (hM (x n))
  have hr : adicRecurrenceMap a (fun n => f (x n)) = 0 := by
    funext n
    change f (x n) - a • f (x (n + 1)) = 0
    rw [← map_smul, hx, sub_self]
  have hn := (isModuleComplete_iff_recurrence_bijective R a N).mp hN
  have hz : (fun n => f (x n)) = 0 := hn.injective (hr.trans (map_zero _).symm)
  exact congrFun hz 0

end SerrePositivity.DerivedCompletion
