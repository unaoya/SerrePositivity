module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotCutRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputListMembership

/-!
模型。文献の定義との比較は後で
# 一出現挿入の出力を比較する左右リスト

概要：Berger–Fresse §2.2.6 の内側切断点までの実際の合成語の左右を計算する。
方針：三ブロックの take・drop を前後の代入語と内側切断の左右へ分ける。
規約：指定色は一出現で、内側切断点は任意。
使われ方：全残り色と全挿入色の出力族の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現挿入の内側切断の左リストは前置語と内側の左リスト（BF §2.2.6）。
方針：実際の合成語の三ブロック分解を切断点まで取る。
規約：内側切断点の文字を含む。
使われ方：出力の零頂点の所属の比較。 -/
lemma compositeInnerPosition_prefix {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p = k)
    (q : Fin (n + e)) :
    (List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val).take
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q).val + 1) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take p.val) (r.segments v.val) ++
        ((List.ofFn v.val).take (q.val + 1)).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_single_slot u v k r hc p hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition]
  rw [Nat.add_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.splice_take_inside _ _ _ _ (by
    simp only [List.length_map, List.length_ofFn]; omega), ← List.map_take]

/-- 概要：一出現挿入の内側切断の右リストは内側の右リストと後置語（BF §2.2.6）。
方針：実際の合成語から前置語と内側切断点より前の部分を除く。
規約：後置語では部分語列は全て消費済み。
使われ方：出力の一頂点の所属の比較。 -/
lemma compositeInnerPosition_suffix {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p = k)
    (q : Fin (n + e)) :
    (List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val).drop
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q).val =
      ((List.ofFn v.val).drop q.val).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).drop (p.val + 1)) [] := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_single_slot u v k r hc p hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.splice_drop_inside _ _ _ _ (by
    simp only [List.length_map, List.length_ofFn]; omega), ← List.map_drop]

/-- 概要：挿入ラベルの像に残りラベルは現れない（BF §2.2.6）。
方針：map の所属を内側ラベルへ戻して両ラベルの非交差を使う。
規約：内側リスト・arity は任意。
使われ方：一出現挿入の左右から内側ブロックを除いて残り色の出力を比較する。 -/
lemma remaining_not_mem_inserted_map {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) (xs : List (Fin n)) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a ∉ xs.map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) := by
  intro hm
  obtain ⟨b, _, he⟩ := List.mem_map.mp hm
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k a b he.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
