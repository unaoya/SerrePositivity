module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapSegments

/-!
模型。文献の定義との比較は後で
# 一部分割と空語の分割

概要：Berger–Fresse §1.2.4 の一出現への挿入と nullary 分岐を同じ有限添字で扱う。
方針：部分長の総和から一部分の長さを一意に決める。
規約：空語の一部分割は空部分語一つ。
使われ方：合成の単一分割の計算と空語挿入の検証に使う。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

/-- 概要：一部分割は語全体を一つの部分語にする（BF §1.2.4）。
方針：唯一の部分長を元の語長にする。
規約：語長零も許す。
使われ方：指定値が一回だけ出現する場合の唯一の合成添字。 -/
def single (l : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 1 l := by
  refine ⟨fun _ => ⟨l, by omega⟩, ?_, ?_⟩
  · intro i
    change 0 < l ∨ l = 0
    omega
  · change (∑ _ : Fin 1, l) + 1 = l + 1
    simp

/-- 概要：一部分割の長さは常に元の語長（BF §1.2.4）。
方針：一項の総和を評価する。
規約：空語も含む。
使われ方：一出現への挿入の全ての分割を一つへまとめる。 -/
lemma single_length {l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 1 l) (i : Fin 1) : (r.val i).val = l := by
  have hs := r.property.2
  simp only [Fin.sum_univ_one] at hs
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  omega

/-- 概要：一部分割は一意（BF §1.2.4）。
方針：全ての有限部分長が元の語長に等しいことを使う。
規約：長さの証明項には依存しない。
使われ方：有限和を一つの項へ簡約する。 -/
lemma eq_single {l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 1 l) : r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single l := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (r.val i).val = l
  exact r.single_length i

/-- 概要：一部分割の部分語は元の全語（BF §1.2.4）。
方針：開始位置零と語長の take を評価する。
規約：値の型は任意。
使われ方：一出現への挿入をリストの置換として計算する。 -/
@[simp] lemma single_segment {α : Type*} {l : ℕ} (v : Fin l → α) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single l).segment v 0 = List.ofFn v := by
  change ((List.ofFn v).drop 0).take l = List.ofFn v
  rw [List.drop_zero]
  exact List.take_of_length_le (by rw [List.length_ofFn])

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition
