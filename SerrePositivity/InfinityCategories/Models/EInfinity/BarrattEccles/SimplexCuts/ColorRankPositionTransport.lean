module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorRankIntervals

/-!
模型。文献の定義との比較は後で
# 同じ位置とその色の証明による元の順位の移送

Berger–Fresse §2.2.6、M14 L12a の同じ語長移送の補助。
位置が等しいとき、同じ色別区間の両端を証明の依存性ごと移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C449c：同じ位置とその色の証明は、同じ最初の順位を与える（BF §2.2.6）。 -/
lemma colorIntervalFirst_congr_position {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a) (h : p = p') :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst s v a p hp = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst s v a p' hp' := by
  subst p'
  rfl

/-- C449d：同じ位置とその色の証明は、同じ最後の順位を与える（BF §2.2.6）。 -/
lemma colorIntervalLast_congr_position {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (hp : v.val p = a) (hp' : v.val p' = a) (h : p = p') :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalLast s v a p hp = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalLast s v a p' hp' := by
  subst p'
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
