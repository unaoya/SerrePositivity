module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecoveryLabels
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWord

/-!
模型。文献の定義との比較は後で
# 合成語の内側射影から全挿入部分語を取り出す

概要：Berger–Fresse §1.5.9 の内側語の復元の最初の段階として元の部分語列を復元する。
方針：残る外側ラベルを除き、各挿入ラベルを元の内側値へ戻す。
規約：この段階では分割境界の共有文字を重複して残す。
使われ方：共有端点の縮約から元の内側語を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：代入語の内側射影は消費した全部分語の連結（BF §1.5.9）。
方針：外側語で帰納し、指定値で部分語を一つ消費する。
規約：部分語数は指定値の出現回数と一致。部分語は空でもよい。
使われ方：合成語から重なる分割の全挿入部分を復元する。 -/
lemma inner_substitute {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (hc : parts.length = xs.count k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) = parts.flatten := by
  induction xs generalizing parts with
  | nil =>
    have hp : parts = [] := List.length_eq_zero_iff.mp (by simpa only [List.count_nil] using hc)
    subst parts
    rfl
  | cons a xs ih =>
    by_cases ha : a = k
    · subst a
      cases parts with
      | nil => simp only [List.length_nil, List.count_cons_self] at hc; omega
      | cons part parts =>
        have ht : parts.length = xs.count k := by simpa only [List.length_cons,
          List.count_cons_self, Nat.add_right_cancel_iff] using hc
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons, List.filterMap_append,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_filterMap_inserted, List.flatten_cons, ih parts ht]
    · have ht : parts.length = xs.count k := by simpa [ha] using hc
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, List.filterMap_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_remaining]
      exact ih parts ht

/-- 概要：実際の合成語の内側射影は元の全分割成分の連結（BF §1.5.9）。
方針：元の分割の個数一致を代入の射影公式へ渡す。
規約：元の内側語の正長性を要求しない。
使われ方：縮約後の元の内側語との一般の一致を証明する。 -/
lemma inner_compositeWord {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) = (r.segments v.val).flatten := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.inner_substitute k (List.ofFn u.val) (r.segments v.val)
    (by rw [r.segments_length]; rfl)

/-- 概要：合成語から内側ラベルだけを戻して連続重複を縮約した語（BF §1.5.9）。
方針：外側ラベルを除き、共有端点の連続重複を一つに縮める。
規約：実際の内側語との一致は分割の全区間を照合して後続で証明する。
使われ方：内側語の一意な逆写像。 -/
def innerWord {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + n))) : List (Fin n) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
