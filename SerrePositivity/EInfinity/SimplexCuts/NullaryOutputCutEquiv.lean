module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointInverse
public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroColor

/-!
# 一出現の色の零次出力を持つ元の全Cutの同値

Berger–Fresse §2.2.6、M14 L12a、報告 §353。
元の一点挿入・削除を実際の出力次数零という条件で包装する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 唯一の色の零次出力は元の一点区間と同値（BF §2.2.6）。 -/
lemma outputDegree_zero_iff_point_of_unique {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word r (m + 2)) (p : Fin (m + 2)) (k : Fin r)
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    outputDegree s v k = 0 ↔ hi s p = lo s p := by
  constructor
  · intro h
    exact outputDegree_zero_hi_eq_lo s v k h p hp
  · intro h
    exact (outputDegree_zero_iff_unique_position_and_point s v k).mpr ⟨p, hp, hu, h⟩

/-- 元の一点挿入・削除は実際の零次出力の全Cutを与える（BF §2.2.6）。 -/
def nullaryOutputCutEquiv (m q r : ℕ) (v : Surjection.Word r (m + 2))
    (p : Fin (m + 2)) (k : Fin r) (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    Cut m q ≃ {s : Cut (m + 1) q // outputDegree s v k = 0} where
  toFun t := ⟨nullaryPointInsertCut t p,
    (outputDegree_zero_iff_point_of_unique _ v p k hp hu).mpr
      (nullaryPointInsertCut_hi_eq_lo t p)⟩
  invFun s := nullaryPointEraseCut s.val p
  left_inv t := nullaryPointEraseCut_insert t p
  right_inv s := Subtype.ext (nullaryPointInsertCut_erase s.val p
    ((outputDegree_zero_iff_point_of_unique s.val v p k hp hu).mp s.property))

end SerrePositivity.EInfinity.SimplexCuts
