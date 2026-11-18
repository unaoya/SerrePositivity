module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWordOccurrence

/-!
模型。文献の定義との比較は後で
# 連続する指定出現の間での代入の一段

概要：Berger–Fresse §1.5.7 の前の出現直後の代入を、間の語・次の挿入語・次の尾部へ分ける。
方針：元の尾部を次の指定出現で切り、間の不出現から部分語を消費しないことを使う。
規約：内側部分語の個数・長さは任意。
使われ方：融合出力と compositeWord の後ろからの帰納を接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：連続出現間の代入を次の指定値で分解（BF §1.5.7）。
方針：実際の尾部を次の出現で分割し、内部の count が零であることを使う。
規約：parts は次の出現に渡す未消費の部分語列。
使われ方：水平・垂直・後続の語を一つの実際の代入へ戻す。 -/
lemma substitute_between_occurrences {m n l : ℕ} (v : Fin l → Fin (m + 1))
    (k : Fin (m + 1)) (i j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) (hij : j.val = i.val + 1)
    (parts : List (List (Fin n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i).val + 1)) parts =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k
        (((List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i).val + 1)).take
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val - ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i).val + 1))) parts ++
        (parts.headD []).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1)) parts.tail := by
  let a := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i).val + 1
  let b := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val
  have hab : a ≤ b := by
    have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono v k (show i < j by change i.val < j.val; omega)
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i).val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val at hm
    omega
  have hp : b < (List.ofFn v).length := by
    simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).isLt
  have hv : (List.ofFn v)[b] = k := by
    simpa only [b, List.getElem_ofFn] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value v k j
  have hd : ((List.ofFn v).drop a).drop (b - a) = k :: (List.ofFn v).drop (b + 1) := by
    rw [List.drop_drop, Nat.add_sub_of_le hab]
    calc
      _ = (List.ofFn v)[b] :: (List.ofFn v).drop (b + 1) := (List.getElem_cons_drop hp).symm
      _ = _ := by rw [hv]
  have hs := List.take_append_drop (b - a) ((List.ofFn v).drop a)
  rw [hd] at hs
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice v k a b (fun p hp hq =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_none_between v k i j hij p (by change _ < p.val; omega) hq)
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_append k (((List.ofFn v).drop a).take (b - a))
    (k :: (List.ofFn v).drop (b + 1)) parts
  rw [hs, List.count_eq_zero.mpr hn, List.drop_zero] at h
  have hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (k :: (List.ofFn v).drop (b + 1)) parts =
      (parts.headD []).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn v).drop (b + 1)) parts.tail := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl]
  rw [hc] at h
  simpa only [List.append_assoc] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
