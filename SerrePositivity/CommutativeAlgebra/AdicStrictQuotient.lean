module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionExact
public import SerrePositivity.CommutativeAlgebra.AdicCompleteness

/-! # 一様なフィルトレーション比較から商の完備性

完備な始域の像について、既存の完備化の完全性から商の分離性を導く。
商の前完備性は全射による移送を再利用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
universe u
variable {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 完備加群間の写像に一様なフィルトレーション比較があれば、その像による商は完備。 -/
theorem isAdicComplete_quotient_range_of_uniform_filtration_bound
    (I : Ideal R) [IsAdicComplete I M] [IsAdicComplete I N] (f : M →ₗ[R] N)
    (hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M)) : IsAdicComplete I (N ⧸ f.range) := by
  let q := f.range.mkQ
  have hex : Function.Exact f q := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ f.range
  have hc := adicCompletion_map_exact_of_uniform_filtration_bound I f q hex
    (Submodule.mkQ_surjective _) hbound
  let := isPrecomplete_of_surjective I q (Submodule.mkQ_surjective _)
  refine { haus' := ?_ }
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective f.range x
  have hy : AdicCompletion.map I q (AdicCompletion.of I N y) = 0 := by
    rw [AdicCompletion.map_of]
    ext n
    simpa [AdicCompletion.of, SModEq.zero, q] using hx n
  obtain ⟨z, hz⟩ := (hc (AdicCompletion.of I N y)).mp hy
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I M z
  rw [AdicCompletion.map_of] at hz
  have hw : f w = y := (AdicCompletion.of_inj (I := I)).mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hw⟩

end SerrePositivity
