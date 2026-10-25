module

public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaFrobenius
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootAdjoinDivisionVariables

/-! # 完全δ環のrank-one元の具体的互換p冪根列 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環で逆Frobeniusをn回適用した指定元の具体的な根候補。 -/
def perfectDeltaRankOneRoot (D : DeltaStructure p A) (hD : D.IsPerfect) (x : A) (n : ℕ) : A :=
  ((D.frobeniusEquiv hD).symm : A → A)^[n] x

/-- 根列の零段は指定元そのもの。 -/
@[simp] theorem perfectDeltaRankOneRoot_zero (D : DeltaStructure p A) (hD : D.IsPerfect) (x : A) :
    perfectDeltaRankOneRoot D hD x 0 = x := rfl

/-- 根列の次段は前段への逆Frobeniusの適用。 -/
theorem perfectDeltaRankOneRoot_succ (D : DeltaStructure p A) (hD : D.IsPerfect)
    (x : A) (n : ℕ) :
    perfectDeltaRankOneRoot D hD x (n + 1) =
      (D.frobeniusEquiv hD).symm (perfectDeltaRankOneRoot D hD x n) :=
  Function.iterate_succ_apply' _ _ _

/-- 指定元のδ値が零なら根列の各段のδ値も零。 -/
theorem perfectDeltaRankOneRoot_delta (D : DeltaStructure p A) (hD : D.IsPerfect)
    (x : A) (hx : D.delta x = 0) (n : ℕ) :
    D.delta (perfectDeltaRankOneRoot D hD x n) = 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [perfectDeltaRankOneRoot_succ]
      have h := D.frobeniusEquiv_symm_isDeltaHom hD (perfectDeltaRankOneRoot D hD x n)
      rw [ih, map_zero] at h
      exact h.symm

/-- rank-one元の次の根のp乗は前の根に一致する。 -/
theorem perfectDeltaRankOneRoot_pow (D : DeltaStructure p A) (hD : D.IsPerfect)
    (x : A) (hx : D.delta x = 0) (n : ℕ) :
    perfectDeltaRankOneRoot D hD x (n + 1) ^ p = perfectDeltaRankOneRoot D hD x n := by
  have h := (D.frobeniusEquiv hD).apply_symm_apply (perfectDeltaRankOneRoot D hD x n)
  change D.frobeniusLift ((D.frobeniusEquiv hD).symm (perfectDeltaRankOneRoot D hD x n)) = _ at h
  rw [← perfectDeltaRankOneRoot_succ] at h
  rw [D.frobeniusLift_apply, perfectDeltaRankOneRoot_delta D hD x hx, mul_zero, add_zero] at h
  exact h

/-- 任意通常環射で根列の像を取っても、同じ互換p冪根条件を満たす。 -/
theorem perfectDeltaRankOneRoot_map_pow {T : Type v} [CommRing T]
    (D : DeltaStructure p A) (hD : D.IsPerfect) (x : A) (hx : D.delta x = 0)
    (q : A →+* T) (n : ℕ) :
    q (perfectDeltaRankOneRoot D hD x (n + 1)) ^ p = q (perfectDeltaRankOneRoot D hD x n) := by
  rw [← map_pow, perfectDeltaRankOneRoot_pow D hD x hx]

end SerrePositivity.BhattScholze
