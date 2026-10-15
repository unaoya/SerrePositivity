import SerrePositivity.CommutativeAlgebra.ModuleDirectLimitFlat
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.moduleDirectLimit_flat
#print axioms SerrePositivity.moduleDirectLimit_flat

-- The exact requested sequential signature: no injectivity or finiteness hypothesis.
example (R : Type*) [CommRing R] (M : ℕ → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (f : ∀ n m, n ≤ m → M n →ₗ[R] M m)
    [DirectedSystem M (f · · ·)] [∀ n, Module.Flat R (M n)] :
    Module.Flat R (Module.DirectLimit M f) :=
  SerrePositivity.moduleDirectLimit_flat M f

-- The public result also covers arbitrary nonempty directed index orders.
example (R ι : Type*) [CommRing R] [Preorder ι] [DecidableEq ι]
    [IsDirectedOrder ι] [Nonempty ι] (M : ι → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (f : ∀ n m, n ≤ m → M n →ₗ[R] M m)
    [DirectedSystem M (f · · ·)] [∀ n, Module.Flat R (M n)] :
    Module.Flat R (Module.DirectLimit M f) :=
  SerrePositivity.moduleDirectLimit_flat M f
