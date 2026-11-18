module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionCutSums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionConcatenation

/-!
模型。文献の定義との比較は後で
# 外側の指定色以外の位置の合成語への埋め込み

概要：Berger–Fresse §2.2.6 の二段切断で、外側の切断点が代入色と異なる場合の合成位置を作る。
方針：元位置の前の代入済み接頭語の長さを位置とし、厳密なリスト分解で値と範囲を証明する。
規約：空の内側語も含み、分割の正規化を変更しない。
使われ方：外側の切断点を保つ二段切断から合成語の切断点への写像。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定色以外の元位置で合成語を接頭語・その文字・接尾語へ分解（BF §2.2.6）。
方針：元の語をその有限位置で分け、代入の連結公式を適用する。
規約：指定色の部分語の個数は元の合成分割と同じ。
使われ方：合成語の実際の切断点の範囲と値の証明。 -/
lemma compositeWord_at_non_slot {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take p.val) (r.segments v.val) ++
        _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u.val p, hp⟩ ::
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).drop (p.val + 1))
            ((r.segments v.val).drop (((List.ofFn u.val).take p.val).count k)) := by
  have hlen : p.val < (List.ofFn u.val).length := by
    simpa only [List.length_ofFn] using p.isLt
  have hs : (List.ofFn u.val).take p.val ++
      u.val p :: (List.ofFn u.val).drop (p.val + 1) = List.ofFn u.val := by
    calc
      _ = (List.ofFn u.val).take p.val ++
          (List.ofFn u.val)[p.val] :: (List.ofFn u.val).drop (p.val + 1) := by
        rw [List.getElem_ofFn]
      _ = List.ofFn u.val := by rw [List.getElem_cons_drop hlen, List.take_append_drop]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_append k ((List.ofFn u.val).take p.val)
    (u.val p :: (List.ofFn u.val).drop (p.val + 1)) (r.segments v.val)
  rw [hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hp] at h
  exact h

/-- 概要：指定色以外の外側位置に対応する合成語の有限位置（BF §2.2.6）。
方針：その位置の前の代入済み接頭語の長さを取り、直後の一文字で範囲を保証する。
規約：内側 arity 零でも定義する。
使われ方：外側切断点が指定色と異なる場合の順方向の位置。 -/
def compositeOuterPosition {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) : Fin (m + n + (d + e)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take p.val) (r.segments v.val)).length, by
    have hl := congrArg List.length (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_non_slot u v k r p hp)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length] at hl
    simp only [List.length_append, List.length_cons] at hl
    omega⟩

/-- 概要：合成語の対応する外側位置の文字は元の残りラベル（BF §2.2.6）。
方針：接頭語の直後の文字として評価する。
規約：部分型の不一致の証明項には依存しない。
使われ方：外側の出力色と合成後の出力色の同定。 -/
lemma compositeOuterPosition_value {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r)[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp).val]'(by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length]; exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp).isLt) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u.val p, hp⟩ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_non_slot u v k r p hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition,
    List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]

/-- 概要：実際の合成基底語の外側位置の文字は元の残りラベル（BF §2.2.6）。
方針：有限基底語の評価を同じ合成リストの評価へ戻す。
規約：基底語の非退化性に正の内側 arity を使う。
使われ方：合成切断の全出力族と二段切断の族の比較。 -/
lemma compositeBasisWord_outerPosition {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u.val p, hp⟩ := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_value u v k r p hp

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
