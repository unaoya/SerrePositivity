module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonSum

/-!
模型。文献の定義との比較は後で
# 頂点境界を除いた table の削除項

概要：Berger–Fresse §1.4.4 の微分保存で残る相殺対象を実際の有限和として指定する。
方針：一文字行の削除位置の補集合を取り、全 Schedule で加算する。
規約：微分保存や残りの和の消滅は仮定しない。
使われ方：Schedule の長さの移動による相殺を示す対象となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一つの table の一文字行以外の削除項（BF §1.4.4）。
方針：抽出失敗は零、成功時は一文字行の位置の補集合で足す。
規約：退化出力の削除項も保持する。
使われ方：残りの相殺項を元の TR の各項に対応させる。 -/
def remainderTerm (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  match h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] with
  | none => 0
  | some out => ∑ k ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))ᶜ,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A out k

/-- 概要：失敗した table の各一文字行に対応する頂点境界項は零（BF §1.4.4）。
方針：一文字行を除く抽出の失敗の同値を適用する。
規約：正規化後の退化と行抽出の失敗を区別する。
使われ方：全 Schedule の分割公式で失敗した項を処理する。 -/
lemma singleton_term_eq_zero_of_none (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = none) :
    (∑ i : Fin (d + 2), if hi : (r.val i).val = 1 then
      (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)
    else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  split
  · rename_i hi
    have he := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singleton_reduction_none_iff w r i hi).mp h
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, he, Option.map_none, Option.getD_none, smul_zero]
  · rfl

/-- 概要：各 TR 項の微分は一文字行の境界項と残りに分かれる（BF §1.4.4）。
方針：抽出成功時は削除位置を分割し、失敗時は両側の項を零にする。
規約：全ての Schedule を含む。
使われ方：全 table の和で頂点境界と相殺対象を分離する。 -/
lemma differential_term_partition (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A w r) =
      (∑ i : Fin (d + 2), if hi : (r.val i).val = 1 then
        (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)
      else 0) + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm
  split
  · rename_i h
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_term, h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singleton_term_eq_zero_of_none A w r h]
    simp only [Option.map_none, Option.getD_none, add_zero]
  · rename_i out h
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_term]
    conv_lhs => rw [h]
    simp only [Option.map_some, Option.getD_some]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rawListDifferential_partition A w r out h

/-- 概要：一文字行の削除と残りの有限和が微分の全体を尽くす（BF §1.4.4）。
方針：各 table の分割を Schedule の和の中へ移す。
規約：arity は正で、nullary は既存の零の公式で別に扱う。
使われ方：一般の微分保存を残りの和の消滅へ帰着する。 -/
lemma differential_onSequence_partition (A : Type u) [CommRing A] {n d : ℕ}
    (hn : 0 < n) (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) =
      (∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), ∑ i : Fin (d + 2), if hi : (r.val i).val = 1 then
        (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)
      else 0) + ∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ite_eq_right (by omega), map_sum]
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_term_partition]
  rw [Finset.sum_add_distrib]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
