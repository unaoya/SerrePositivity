module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.FirstOccurrences
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Basic

/-!
模型。文献の定義との比較は後で
# 全射語から復元する置換の行

概要：Berger–Fresse §1.4.2 の逆像候補の各置換を、語の任意の位置で構成する。
方針：既に最終出現を通過した値と、残りの語の最初の出現を順に連結する。
規約：前半は最終出現の順、後半は最初の出現の順。空語も許す。
使われ方：table の各行の開始位置で評価し、TR の全射性の逆像を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {α : Type*} [DecidableEq α]

/-- 概要：指定位置までに最終出現が終わった値の列（BF §1.4.2）。
方針：先頭部分から最後の出現を残し、尾部にも現れる値を除く。
規約：位置 p は先頭から読んだ文字数で、零を含む。
使われ方：復元する置換の既に確定した前半を指定する。 -/
def pastFinals (xs : List α) (p : ℕ) : List α :=
  (xs.take p).dedup.filter (fun a => a ∉ xs.drop p)

/-- 概要：指定位置での復元する置換の値の列（BF §1.4.2）。
方針：確定した最終出現と尾部の最初の出現を連結する。
規約：全射性を要求せず、任意の有限語から構成する。
使われ方：全射語では全ての値を一度ずつ含む置換となる。 -/
def canonicalRow (xs : List α) (p : ℕ) : List α :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences (xs.drop p)

/-- 概要：確定した最終出現の列の所属条件（BF §1.4.2）。
方針：重複除去と filter の所属判定を簡約する。
規約：尾部にもう現れない値だけを取る。
使われ方：前半と後半の共通値がないことを証明する。 -/
@[simp] lemma mem_pastFinals (xs : List α) (p : ℕ) (a : α) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p ↔ a ∈ xs.take p ∧ a ∉ xs.drop p := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals, List.mem_filter, List.mem_dedup, decide_eq_true_eq]

/-- 概要：復元する行の値の集合は元の語の値の集合（BF §1.4.2）。
方針：尾部への所属で分岐し、take と drop の分割を使う。
規約：p が語の長さより大きくても成立する。
使われ方：全射語から作る行の全射性を与える。 -/
@[simp] lemma mem_canonicalRow (xs : List α) (p : ℕ) (a : α) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs p ↔ a ∈ xs := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow, List.mem_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_pastFinals, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_firstOccurrences]
  have h : a ∈ xs.take p ∨ a ∈ xs.drop p ↔ a ∈ xs := by
    rw [← List.mem_append, List.take_append_drop]
  tauto

/-- 概要：復元する行には値の重複がない（BF §1.4.2）。
方針：二つの部分はそれぞれ重複せず、所属条件によって互いに素である。
規約：元の語は重複してよい。
使われ方：全射語から置換を得る単射性の証明。 -/
lemma canonicalRow_nodup (xs : List α) (p : ℕ) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs p).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_dedup _).filter _, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_nodup _, ?_⟩
  intro a ha b hb hab
  subst b
  exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_pastFinals xs p a).mp ha).2 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_firstOccurrences a _).mp hb)

/-- 概要：語の開始位置での復元行は最初の出現の順（BF §1.4.2）。
方針：空の先頭部分を簡約する。
規約：空語も含む。
使われ方：最初の頂点置換の計算に用いる。 -/
@[simp] lemma canonicalRow_zero (xs : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs 0 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences xs := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals]

/-- 概要：語の終端での復元行は最終出現の順（BF §1.4.2）。
方針：空の尾部を簡約する。
規約：dedup は最終出現を残す。
使われ方：最後の table 行と原典の最終出現の置換を比較する。 -/
@[simp] lemma canonicalRow_length (xs : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs xs.length = xs.dedup := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
