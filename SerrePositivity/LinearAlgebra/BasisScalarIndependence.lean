module

public import Mathlib.RingTheory.AlgebraTower

/-! # 係数の生成系を展開して独立性を戻す

`S` が `R` 上で族 `b` に張られるとき、積の族 `b k • v i` が `R` 上独立なら、`v` は `S` 上独立。
基底でなく生成系で足り、添字の有限性も不要。
`b` が基底なら、Mathlib の `linearIndependent_smul`（順向き）と合わせて同値になる。
添字の順（`κ × ι`、係数側が先）は `linearIndependent_smul` に揃える。
-/

@[expose] public section
namespace SerrePositivity

variable {R S M ι κ : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
  [Module R S] [Module R M] [Module S M] [IsScalarTower R S M]

/-- 係数の生成系との積の族が小さい係数環上で独立なら、元の族は大きい係数環上で独立。 -/
theorem linearIndependent_of_smul_of_span_eq_top {b : κ → S}
    (hb : Submodule.span R (Set.range b) = ⊤) {v : ι → M}
    (h : LinearIndependent R fun p : κ × ι ↦ b p.1 • v p.2) : LinearIndependent S v := by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι × κ ↦ b p.2 • v p.1) rfl,
    LinearIndependent, Finsupp.linearCombination_smul] at h
  have hB : Function.Surjective (Finsupp.linearCombination R b) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hb]
  exact Function.Injective.of_comp_right h
    ((Finsupp.mapRange_surjective _ (map_zero _) hB).comp (Finsupp.curryLinearEquiv R).surjective)

/-- 係数の基底との積の族の小さい係数環上の独立性は、元の族の大きい係数環上の独立性と同値。 -/
theorem basis_linearIndependent_smul_iff (b : Module.Basis κ R S) {v : ι → M} :
    LinearIndependent R (fun p : κ × ι ↦ b p.1 • v p.2) ↔ LinearIndependent S v :=
  ⟨linearIndependent_of_smul_of_span_eq_top b.span_eq, linearIndependent_smul b.linearIndependent⟩

end SerrePositivity
