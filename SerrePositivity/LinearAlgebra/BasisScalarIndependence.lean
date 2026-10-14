module

public import Mathlib.RingTheory.AlgebraTower

/-! # 係数基底を展開して独立性を戻す

係数環の基底との積が小さい係数環上で独立なら、元の族は大きい係数環上で独立。
基底の添字の有限性は不要。
-/

@[expose] public section
namespace SerrePositivity

theorem linearIndependent_of_basis_smul
    {R S M ι κ : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (B : Module.Basis κ R S) (v : ι → M)
    (h : LinearIndependent R (fun z : ι × κ ↦ B z.2 • v z.1)) :
    LinearIndependent S v := by
  rw [LinearIndependent, Finsupp.linearCombination_smul] at h
  rw [LinearIndependent]
  have hB : Function.Surjective (Finsupp.linearCombination R B) :=
    fun x ↦ ⟨B.repr x, B.linearCombination_repr x⟩
  let F : (ι × κ →₀ R) → (ι →₀ S) := fun a ↦
    Finsupp.mapRange (Finsupp.linearCombination R B) (map_zero _)
      (Finsupp.curryLinearEquiv R a)
  have hF : Function.Surjective F := (Finsupp.mapRange_surjective _ (map_zero _) hB).comp
    (Finsupp.curryLinearEquiv R).surjective
  exact Function.Injective.of_comp_right (f := Finsupp.linearCombination S v) (g := F) h hF

end SerrePositivity
