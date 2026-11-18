module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NullaryRawWord
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RemainingPositionOrder
public import Mathlib.Order.Preorder.Finite

/-!
模型。文献の定義との比較は後で
# 実際の空語合成の指定位置と色の削除

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §330。
元のcompositeOuterPositionの順序を保ち、同じ有限自己順序単射の一意性を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元のnullaryの残り色の番号は、指定色を飛ばす順序単射の逆（BF §2.2.6）。 -/
lemma succAbove_remainingPosition_nullary (m : ℕ) (k : Fin (m + 1))
    (a : {j : Fin (m + 1) // j ≠ k}) :
    k.succAbove (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a) = a.val := by
  have ha : a.val.val ≠ k.val := fun h => a.property (Fin.ext h)
  have hv := _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_val m 0 k a
  by_cases hlt : a.val.val < k.val
  · have he : (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a).val = a.val.val := by
      simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.remainingValue, ite_eq_left hlt] using hv
    have hc : (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a).castSucc < k := by
      change (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a).val < k.val
      rwa [he]
    rw [Fin.succAbove_of_castSucc_lt _ _ hc]
    exact Fin.ext he
  · have he : (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a).val = a.val.val - 1 := by
      simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.remainingValue, ite_eq_right hlt, Nat.add_zero] using hv
    have hc : k ≤ (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a).castSucc := by
      change k.val ≤ (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a).val
      rw [he]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hc]
    apply Fin.ext
    change (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k a).val + 1 = a.val.val
    omega

/-- 同じ一出現を消した後の実際の合成位置は、残る位置の元の番号（BF §2.2.6）。 -/
lemma compositeOuterPosition_nullary_erase {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (m + d))
    (hne : u.val (Fin.cast (by omega : m + d + 1 = m + 1 + d)
      ((Fin.cast (by omega : m + 1 + d = m + d + 1) p).succAbove i)) ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r
      (Fin.cast (by omega : m + d + 1 = m + 1 + d)
        ((Fin.cast (by omega : m + 1 + d = m + d + 1) p).succAbove i)) hne = i := by
  let ep : Fin (m + d + 1) := Fin.cast (by omega) p
  let j : Fin (m + d) → Fin (m + 1 + d) := fun a => Fin.cast (by omega) (ep.succAbove a)
  have hj (a : Fin (m + d)) : u.val (j a) ≠ k := by
    intro h
    have he := hu (j a) h
    have he' : ep.succAbove a = ep := by
      apply Fin.ext
      have hv : (j a).val = p.val := congrArg Fin.val he
      exact hv
    exact Fin.succAbove_ne ep a he'
  let f : Fin (m + d) → Fin (m + d) := fun a =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r (j a) (hj a)
  have hf : StrictMono f := by
    intro a b hab
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r (j a) (hj a) <
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r (j b) (hj b)
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt u v k r (j a) (j b) (hj a) (hj b)
    exact Fin.strictMono_succAbove ep hab
  exact hf.apply_eq

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
