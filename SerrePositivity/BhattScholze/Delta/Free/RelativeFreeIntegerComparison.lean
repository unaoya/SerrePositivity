module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing

/-! # 相対自由構成と自由整数δ環の比較

基底が整数環の場合、相対W₂切断によるδ構造と、前段のFrobenius持上げによる
自由整数δ構造は一致する。二つの構成を互換なAPIとして利用するための比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 整数上の相対自由δ構造は既存の自由整数δ構造と一致する。
Frobeniusを係数・変数上で比較し、整数多項式環のp正則性による一意性を使う。 -/
theorem relativeFreeDeltaStructure_int_eq (D : DeltaStructure p ℤ) :
    relativeFreeDeltaStructure σ D = freeDeltaStructure p σ := by
  have hφ : (relativeFreeDeltaStructure σ D).frobeniusLift = freeDeltaFrobenius p σ := by
    apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
    rintro ⟨s, n⟩
    rw [DeltaStructure.frobeniusLift_apply, relativeFreeDeltaStructure_delta_X,
      freeDeltaFrobenius_X]
  exact (existsUnique_freeDeltaStructure p σ).choose_spec.2 _ hφ

end SerrePositivity.BhattScholze
