module

public import SerrePositivity.CommutativeAlgebra.Adic.BoundedTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # 有界冪ねじれの下での導来完備性と古典的完備性 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 有界f冪ねじれを持つ導来完備加群は古典的f進完備。 -/
theorem isAdicComplete_of_isModuleComplete_of_bounded_torsion (f : R)
    (M : ModuleCat.{u} R)
    (hM : IsModuleComplete R f M)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0) :
    IsAdicComplete (Ideal.span {f}) M := by
  have h := (isModuleComplete_iff_recurrence_bijective R f M).mp hM
  let := isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion f hbounded h.1
  let := isPrecomplete_of_adicRecurrenceMap_surjective f h.2
  exact ⟨⟩

/-- 有界ねじれの下では、古典的完備性と実導来圏での完備性が同値。 -/
theorem isModuleComplete_iff_isAdicComplete_of_bounded_torsion (f : R)
    (M : ModuleCat.{u} R)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0) :
    IsModuleComplete R f M ↔ IsAdicComplete (Ideal.span {f}) M := by
  constructor
  · exact fun h ↦ isAdicComplete_of_isModuleComplete_of_bounded_torsion R f M h hbounded
  · intro h
    let := h
    exact isModuleComplete_of_isAdicComplete R f M

/-- 自然数pの像についての環版。素数性やp正則性は不要。 -/
theorem isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion (p : ℕ)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R,
      (p : R) ^ n * x = 0 → (p : R) ^ N * x = 0) :
    IsModuleComplete R (p : R) (ModuleCat.of R R) ↔
      IsAdicComplete (Ideal.span {(p : R)}) R :=
  isModuleComplete_iff_isAdicComplete_of_bounded_torsion R (p : R)
    (ModuleCat.of R R) hbounded

end SerrePositivity.DerivedCompletion
