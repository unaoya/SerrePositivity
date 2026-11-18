module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PreviousVertexPositions

/-!
模型。文献の定義との比較は後で
# 同色の直前の面に移したBF境界符号

Berger–Fresse §2.2.7、M14 L09a。
同じ色の連続する面番号の差一を使い、最後の非活動頂点も活動頂点の式へ運ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts (positionInversionCount)

lemma outputBoundarySignAt_rank {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v.val * (-1 : ℤ) ^
      ((∑ c ∈ Finset.univ.filter (fun c : Fin r => c < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v c) +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) k) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySign
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank_symm_colorPositionEquiv s v k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv_symm_color]

/-- C116：同色の直前の頂点の境界符号とは、面番号が一つ違うので反対。 -/
lemma outputBoundarySignAt_previous {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v k =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k h) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_value (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k h
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank_previousVertex s v.val k h
  rw [hc] at hr
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_rank, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_rank, hc, hr]
  simp only [← Nat.add_assoc, pow_succ, mul_neg, mul_one]

/-- C117：直前の活動頂点の逆転集合で、指定頂点のBF境界符号を計算する。 -/
lemma outputBoundarySignAt_via_previous {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v k = -
      ((-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v.val *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val)
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val).erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k h)) *
        (-1 : ℤ) ^ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val).filter
          (fun j => j < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k h)).card) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_previous s v k h,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_of_active s v _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_active s v.val k h)]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
