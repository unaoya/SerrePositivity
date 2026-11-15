module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrencePosition
public import SerrePositivity.EInfinity.Surjection.OccurrenceCompleteness

/-!
# 元の指定色の出現位置が区切りになる条件

Berger–Fresse §1.2.2・§1.2.4、M14 L12a の C452。
元の列挙済みの出現に次の番号があることを、そのまま区切りの定義で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の出現位置が区切りなのは、次の同色出現があるとき（BF §1.2.2）。 -/
lemma positiveOccurrencePosition_caesura_iff {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i) ↔
      i.val + 1 < Surjection.occurrenceCount u.val k := by
  constructor
  · rintro ⟨p, hp, hvp⟩
    let p' : Fin ((m + 1) + d) := ⟨p.val, by have hb := p.isLt; omega⟩
    have hv : u.val p' = k :=
      (word_eq_mp_value (by omega : (m + 1) + d = m + d + 1) u p p' rfl).symm.trans
        (hvp.trans (positiveOccurrencePosition_value u k i))
    obtain ⟨j, hj⟩ := Surjection.occurrenceAt_complete u.val k p' hv
    have hj' : positiveOccurrencePosition u k j = p := by
      apply Fin.ext
      change (Surjection.occurrenceAt u.val k j).val = p.val
      exact congrArg (fun x : Fin ((m + 1) + d) => x.val) hj
    have hij : i < j := (positiveOccurrencePosition_strictMono u k).lt_iff_lt.mp
      (by rw [hj']; exact hp)
    have hb := j.isLt
    omega
  · intro h
    let j : Fin (Surjection.occurrenceCount u.val k) := ⟨i.val + 1, h⟩
    refine ⟨positiveOccurrencePosition u k j,
      positiveOccurrencePosition_strictMono u k (show i < j by change i.val < i.val + 1; omega), ?_⟩
    exact (positiveOccurrencePosition_value u k j).trans
      (positiveOccurrencePosition_value u k i).symm

end SerrePositivity.EInfinity.SimplexCuts
