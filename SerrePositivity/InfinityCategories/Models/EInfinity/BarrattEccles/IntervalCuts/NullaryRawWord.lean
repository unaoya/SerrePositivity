module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotCutRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.NullaryErasure

/-!
模型。文献の定義との比較は後で
# 空語合成の正規化前の有限語

概要：Berger–Fresse §2.2.6 の nullary 合成を退化し得る実際の有限語で扱う。
方針：合成リストを長さの公式で有限関数へ移し、左右の切断リストを比較する。
規約：非退化性を仮定せず、出力 arity 零も含む。
使われ方：空語合成の辺成分を全ての非零切断上の和へ展開する。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：空語の合成リストを読む正規化前の有限関数（BF §1.2.4・§2.2.6）。
方針：実際の合成語長により添字を固定する。
規約：退化語もそのまま保持する。
使われ方：nullary の合成生成元と切断の共通の入力。 -/
def nullaryRawWord {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) :
    Fin (m + d) → Fin m :=
  fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r)[j.val]'(by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length]; exact j.isLt)

/-- 概要：空語合成の有限関数のリスト表示は実際の合成リスト（BF §1.2.4）。
方針：語長と各有限位置の値を比較する。
規約：退化・空語を含む。
使われ方：有限関数の切断をリストの take・drop へ移す。 -/
lemma nullaryRawWord_list {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) :
    List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn, Nat.add_zero] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length u v k r).symm
  · intro j hj hj'
    simp only [List.getElem_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord]

/-- 概要：空語合成の有限関数は全射（BF §1.2.4）。
方針：合成リストの既存の全射性を有限位置の移送で戻す。
規約：非退化性は要求しない。
使われ方：正規化生成元の辺成分で非全射分岐を除く。 -/
lemma nullaryRawWord_surjective {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r) := by
  intro a
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_surjective u v k r a
  exact ⟨Fin.cast (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length u v k r) j, hj⟩

/-- 概要：実際の空語合成項は有限関数の正規化生成元（BF §1.2.4）。
方針：合成語のリスト表示と ofFn の正規化公式を使う。
規約：退化の場合は既存の generator が零へ送る。
使われ方：nullary の実際の左辺を非零切断和へ移す。 -/
lemma compositeGenerator_nullaryRawWord (A : Type u) [CommRing A] {m d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A u v k r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (d := d) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_list u v k r, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn]

/-- 概要：空語合成の残り位置の文字は元の色の詰め直し（BF §2.2.6）。
方針：合成リスト上の残り位置の評価を有限関数で読む。
規約：元の位置の色は指定色と異なる。
使われ方：切断点の復元と全出力族・逆転数の比較。 -/
lemma nullaryRawWord_outerPosition {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) (p : Fin (m + 1 + d))
    (hp : u.val p ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k ⟨u.val p, hp⟩ :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_value u v k r p hp

/-- 概要：空語合成の残り切断点までのリストは元の左側への空語代入（BF §2.2.6）。
方針：正規化前のリストを残り位置で分解して接頭語長を評価する。
規約：切断点を含む。
使われ方：nullary の非零切断の左単射性を比較する。 -/
lemma nullaryRawWord_prefix {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    (List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r)).take
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp).val + 1) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take (p.val + 1)) (r.segments v.val) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_non_slot u v k r p hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_take_at_non_slot u.val k p hp,
    List.take_length_add_append, List.take_succ_cons, List.take_zero]

/-- 概要：空語合成の残り切断点以後のリストは元の右側への空語代入（BF §2.2.6）。
方針：接頭語を drop し、元の指定位置の残り文字を先頭に保つ。
規約：切断点を含み、消費済み部分語だけを除く。
使われ方：nullary の非零切断の右単射性を比較する。 -/
lemma nullaryRawWord_suffix {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    (List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r)).drop
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp).val =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).drop p.val)
        ((r.segments v.val).drop (((List.ofFn u.val).take p.val).count k)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_non_slot u v k r p hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_drop_at_non_slot u.val k p hp,
    List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero, List.nil_append]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
