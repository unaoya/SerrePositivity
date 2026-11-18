module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.WordCrossWeightBalance
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OtherActivePrefixCounts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ActiveBoundarySigns
public import Mathlib.Data.Nat.ModEq

/-!
模型。文献の定義との比較は後で
# 元の交差寄与と同じnativeなB・Pのmod 2

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ水平fiberの濃度で、二度数える先行小色をmod 2で消す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の交差寄与は、同じ先行他色数と小色の出力次数の和に合同（BF §2.2.6）。 -/
lemma cross_intervalLength_modeq_prefix {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin r) (p : Fin (m + 1)) (hp : v.val p = k)
    (x : Fin (m + q + 1)) (hx : s.horizontal x = p) :
    Nat.ModEq 2
      (∑ j : {j : Fin (m + 1) // v.val j ≠ k},
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm v.val j.val p +
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm v.val p j.val) * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s v.val j.val)
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val).filter (fun z => z < x ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val z ≠ k)).card +
        ∑ b ∈ Finset.univ.filter (fun b : Fin r => b < k), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v b) := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_cross_weight_balance v.val k p hp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s v.val)
  have hB := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.other_active_prefix_card_eq_weighted s v.val k p hp x hx
  have hPH := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.active_filter_horizontal_card s v.val (fun j => v.val j < k)
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val).filter (fun z => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val z < k)).card = _ at hPH
  have hP := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixOutputDegree_eq_active_card s v k).trans hPH
  simp only [← hB, ← hP] at he
  unfold Nat.ModEq
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
