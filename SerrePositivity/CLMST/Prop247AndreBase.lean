module

public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatEquiv
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle

/-! # Prop 2.4.7：証明済み André 拡大の実降下データ

BS Thm 7.14 の証明済み公開入口を使い、既存 D1〜D6 が受け取る
元の baseChangeScalarModule に対する p 完全忠実平坦性を供給する。
拡大は R から一度選び、S・g・剰余段に依存させない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST

/-- 元の R から選ぶ、perfectoid・絶対整閉な André 拡大と実降下用の完全忠実平坦性。
存在を新しい仮定・引用とせず、証明済み BS Thm 7.14 から供給する。 -/
theorem prop247_exists_andre_descent_base
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
      IsIntegralPerfectoid B p ∧ IsAbsolutelyIntegrallyClosed B ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
        (baseChangeScalarModule (algebraMap R B)) := by
  obtain ⟨B, hB, hRB, hperf, hflat, hAIC⟩ :=
    BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  letI := hB
  letI := hRB
  exact ⟨B, hB, hRB, hperf, hAIC,
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)})
      (algebraSelfRestrictionIso R B).toLinearEquiv.symm hflat⟩

end SerrePositivity.CLMST
