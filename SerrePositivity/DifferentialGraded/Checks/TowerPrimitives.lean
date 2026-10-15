module
public import SerrePositivity.DifferentialGraded.Complexes.TowerPrimitives

/-! # U10b5a：全射的acyclic可算塔での互換な原像 -/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A]

example (K : ℕ → Complex A) (r : ∀ n, K (n + 1) ⟶ K n)
    (hK : ∀ n, (K n).Acyclic)
    (hr : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((r n).f q)) (q : ℤ)
    (z : ∀ n, (K n).X q) (hz : ∀ n, (K n).d q (q + 1) (z n) = 0)
    (hcompat : ∀ n, (r n).f q (z (n + 1)) = z n) :
    ∃ t : ∀ n, (K n).X (q - 1),
      (∀ n, (K n).d (q - 1) q (t n) = z n) ∧
      (∀ n, (r n).f (q - 1) (t (n + 1)) = t n) :=
  complexTower_compatible_primitives K r hK hr q z hz hcompat

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms complexAcyclic_boundary
#print axioms complexTower_primitive_step
#print axioms complexTower_compatible_primitives
