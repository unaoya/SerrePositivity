module

public import Mathlib.LinearAlgebra.Basis.Basic

/-! # 基底の一方向の線形包の飽和性

非零スカラーを掛けた元が一つの基底元の線形包に属すれば、元も同じ線形包に属す。
-/

@[expose] public section
namespace SerrePositivity

/-- 基底の一方向の線形包は、非零スカラーによる除算について飽和。 -/
theorem basis_mem_span_singleton_of_smul_mem
    {R M ι : Type*} [CommSemiring R] [NoZeroDivisors R]
    [AddCommMonoid M] [Module R M] (B : Module.Basis ι R M) (i : ι)
    {a : R} (ha : a ≠ 0) {x : M} (hx : a • x ∈ R ∙ B i) : x ∈ R ∙ B i := by
  classical
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  apply Submodule.mem_span_singleton.mpr
  refine ⟨B.repr x i, B.repr.injective ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · have he := congrArg (fun v ↦ B.repr v j) hc
    have hz : B.repr x j = 0 := by
      have he' : a * B.repr x j = 0 := by
        simpa [Finsupp.single_apply, Ne.symm hji] using he.symm
      exact (mul_eq_zero.mp he').resolve_left ha
    simp [Ne.symm hji, hz]

end SerrePositivity
