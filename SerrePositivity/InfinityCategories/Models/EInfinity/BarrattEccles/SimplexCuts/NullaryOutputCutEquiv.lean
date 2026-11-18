module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointInverse
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryZeroColor

/-!
模型。文献の定義との比較は後で
# 一出現の色の零次出力を持つ元の全Cutの同値

Berger–Fresse §2.2.6、M14 L12a、報告 §353。
元の一点挿入・削除を実際の出力次数零という条件で包装する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 唯一の色の零次出力は元の一点区間と同値（BF §2.2.6）。 -/
lemma outputDegree_zero_iff_point_of_unique {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (p : Fin (m + 2)) (k : Fin r)
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0 ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p := by
  constructor
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_hi_eq_lo s v k h p hp
  · intro h
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_iff_unique_position_and_point s v k).mpr ⟨p, hp, hu, h⟩

/-- 元の一点挿入・削除は実際の零次出力の全Cutを与える（BF §2.2.6）。 -/
def nullaryOutputCutEquiv (m q r : ℕ) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2))
    (p : Fin (m + 2)) (k : Fin r) (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q ≃ {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0} where
  toFun t := ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut t p,
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_iff_point_of_unique _ v p k hp hu).mpr
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_hi_eq_lo t p)⟩
  invFun s := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s.val p
  left_inv t := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_insert t p
  right_inv s := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_erase s.val p
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_iff_point_of_unique s.val v p k hp hu).mp s.property))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
