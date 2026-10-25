module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaUniversal
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaFrobenius

/-! # pねじれを許すFrobeniusのδ射性

自由整数δ環のp正則性で確認した恒等式を任意のδ環へ評価する。
完全化の反復図式に追加のp正則性を要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 任意のδ環でFrobenius持上げとδは可換。 -/
theorem frobeniusLift_delta (D : DeltaStructure p A) (x : A) :
    D.frobeniusLift (D.delta x) = D.delta (D.frobeniusLift x) := by
  let F := freeDeltaStructure p Unit
  let f := freeDeltaEval D (fun _ : Unit ↦ x)
  have hf : F.IsDeltaHom D f := freeDeltaEval_isDeltaHom D (fun _ : Unit ↦ x)
  let t : FreeDeltaRing Unit := MvPolynomial.X ((), 0)
  have ht : f t = x := by simp [f, t]
  have h := congrArg f (F.isDeltaHom_frobeniusLift
    (freeDeltaRing_p_mul_injective p Unit) t)
  rw [hf.map_frobeniusLift, hf, hf, hf.map_frobeniusLift, ht] at h
  exact h

/-- 任意のδ環のFrobenius持上げはδ射。p正則性を要求しない版。 -/
theorem isDeltaHom_frobeniusLift_general (D : DeltaStructure p A) :
    D.IsDeltaHom D D.frobeniusLift := D.frobeniusLift_delta

/-- Frobeniusの全ての反復はδと可換。 -/
theorem frobeniusLift_iterate_delta (D : DeltaStructure p A) (n : ℕ) (x : A) :
    (D.frobeniusLift : A → A)^[n] (D.delta x) =
      D.delta ((D.frobeniusLift : A → A)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, D.frobeniusLift_delta]

end SerrePositivity.BhattScholze.DeltaStructure
