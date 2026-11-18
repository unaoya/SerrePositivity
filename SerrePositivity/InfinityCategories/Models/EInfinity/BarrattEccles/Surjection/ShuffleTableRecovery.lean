module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterTraceNondegenerate
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleComponent
public import Mathlib.Data.List.ChainOfFn

/-!
模型。文献の定義との比較は後で
# 実際の shuffle 経路上の非退化外側表の復元

概要：Berger–Fresse §1.5.8 の任意の実際の shuffle 経路表に外側復元を適用する。
方針：経路の単位ステップから隣接行の一方の置換が固定されることを導く。
規約：元の Schedule と実際の経路表の成功を入力とし、経路一致の仮定を追加しない。
使われ方：TR 部分合成保存の逆構成で全ての経路上の成功項から外側候補を得る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：実際の経路と Schedule が定める元の内外置換と行長の列（BF §1.5.8）。
方針：各経路頂点の水平・垂直座標で元の置換を評価する。
規約：頂点の順序と元の Schedule の行長をそのまま保持する。
使われ方：一般の mixedTable 復元へ実際の shuffle 入力を渡す。 -/
def shuffleTableEntries {m n d e : ℕ} (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) :
    List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ) :=
  List.ofFn (fun i => (outer (s.horizontal i), inner (s.vertical i), (r.val i).val))

/-- 概要：経路データから作る mixedTable は元の実際の経路表（BF §1.5.8）。
方針：二つの ofFn の評価を一致させる。
規約：行長と逆置換の規約も元の rows に一致する。
使われ方：元の成功を復元界面の成功条件へそのまま移す。 -/
lemma shuffleTableEntries_rows {m n d e : ℕ} (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
        (inner (s.vertical i))) r := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries, List.map_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows]
  rfl

/-- 概要：実際の shuffle 表では隣接する内外置換の一方が固定される（BF §1.5.8）。
方針：各辺の単位ステップを水平・垂直に分け、固定座標で元の置換を評価する。
規約：元の二つの置換列に非退化性などを課さない。
使われ方：圧縮外側語の非退化性の隣接条件を追加仮定なしで供給する。 -/
lemma shuffleTableEntries_axis {m n d e : ℕ} (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r).IsChain
      (fun p q => p.1 = q.1 ∨ p.2.1 = q.2.1) := by
  apply List.isChain_ofFn.mpr
  intro i hi
  let j : Fin (d + e) := ⟨i, by omega⟩
  rcases s.unit_step j with h | h
  · exact Or.inr (congrArg inner h.2.symm)
  · exact Or.inl (congrArg outer h.1.symm)

/-- 概要：任意の実際の非退化な成功 shuffle 表から非退化外側語を復元する（BF §1.5.8）。
方針：実際の経路表の同定と単位ステップの隣接条件を全外側復元へ渡す。
規約：復元表は同じ外側置換の隣接重複を融合する。元の外側行数との一致は後続。
使われ方：一般の TR 部分合成保存の全実際の経路項の逆構成。 -/
lemma shuffle_outer_recovery {m n d e : ℕ} (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun i => permutationComposition m n k (outer (s.horizontal i))
      (inner (s.vertical i))) r) removed = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ picked finish,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r)) removed picked finish ∧
      out = picked.flatten ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) ∧ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).IsChain (· ≠ ·) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.compressed_outer_table_nondegenerate k _ removed out
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries_rows]; exact h) hc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries_axis s outer inner r)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
