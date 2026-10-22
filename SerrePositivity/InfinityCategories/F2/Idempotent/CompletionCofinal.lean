module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionLeftCofinal
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionOpposite

/-!
概要：元の全部分圏による冪等完備化の包含は、余極限を計算する向きにも cofinal。
方針：同じ反転射の極限側の Quillen A を、元の射の right cofinal 性へ戻す。
規約：元の包含そのものを判定し、普遍性の仮定を追加しない。
使われ方：HTT 5.1.4.6、元の全標準左 Kan 余錐の普遍性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全部分圏の冪等完備化の包含は right cofinal。 -/
lemma IsIdempotentCompletion.isRightCofinal {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : IsIdempotentCompletion f) : IsRightCofinal f := by
  have h := IsIdempotentCompletion.isLeftCofinal (SSet.opFunctor.map f)
    (IsIdempotentCompletion.op f hf)
  exact (isRightCofinal_iff_isLeftCofinal_op f).mpr h

end SerrePositivity.InfinityCategories.F2.Idempotent
