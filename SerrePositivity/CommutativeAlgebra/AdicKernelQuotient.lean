module

public import SerrePositivity.CommutativeAlgebra.AdicCompleteness

/-! # 分離加群への線形写像の核による商の完備性

前完備性は既存の全射による移送を使い、分離性は核による商の埋込みで確認する。
Noether性や核の有限生成性を要求しない。
-/

public section
namespace SerrePositivity
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- 分離加群への単射線形写像があれば、定義域も分離している。 -/
theorem isHausdorff_of_injective_linearMap (I : Ideal R) [IsHausdorff I N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) : IsHausdorff I M := by
  refine ⟨fun x hx ↦ hf ?_⟩
  rw [map_zero]
  apply IsHausdorff.haus (inferInstance : IsHausdorff I N) (f x)
  intro n
  simpa only [map_zero] using smodEq_map_pow I f (hx n)

/-- 前完備加群から分離加群への線形写像の核による商は完備。 -/
theorem isAdicComplete_quotient_ker (I : Ideal R) [IsPrecomplete I M]
    [IsHausdorff I N] (f : M →ₗ[R] N) : IsAdicComplete I (M ⧸ LinearMap.ker f) := by
  let k := (LinearMap.ker f).liftQ f le_rfl
  have hk : Function.Injective k := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ f le_rfl le_rfl
  let := isHausdorff_of_injective_linearMap I k hk
  let := isPrecomplete_of_surjective I (LinearMap.ker f).mkQ
    (Submodule.mkQ_surjective _)
  exact ⟨⟩

end SerrePositivity
