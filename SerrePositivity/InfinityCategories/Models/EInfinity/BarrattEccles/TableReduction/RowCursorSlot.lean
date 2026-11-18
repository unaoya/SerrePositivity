module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorSplit
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RemainingLettersValues

/-!
模型。文献の定義との比較は後で
# 元の抽出行の指定値の前後を代入用の文字列へ移す

概要：Berger–Fresse §1.5.7 の外側指定値を実際の利用可能行の一出現として取り出す。
方針：現在行の重複のなさから前後の不出現を得て、既存 remainingLetters で部分型へ移す。
規約：現在行の指定値は元の出力位置で指定する。
使われ方：substitute_one_slot と合成抽出の三種類の成功規則への具体的な入力。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：元の現在行の指定出力文字はまだ除外されていない（BF §1.5.7）。
方針：利用可能行の同じ位置の値が filter の条件を満たすことを使う。
規約：現在行末も含む。
使われ方：合成行の代入表示の未除外条件を元の成功から供給する。 -/
lemma value_not_removed {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (n + d)) (j : Fin (r.val i).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val) : v p ∉ b.removed := by
  have hb : j.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).length := by
    have := b.bound; have := j.isLt; omega
  have hm : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i))[j.val] ∈
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i) := List.getElem_mem hb
  rw [← b.value p j hp] at hm
  exact of_decide_eq_true (List.mem_filter.mp hm).2

/-- 概要：元の利用可能行は指定値を一つ挟む部分型の前後に分かれる（BF §1.5.7）。
方針：行の単射性から前後に指定値がないことを示し、残りラベルの部分型へ持ち上げる。
規約：前半の長さは実際の行内列番号。
使われ方：実際の元の成功表から一出現代入に必要な前半・後半を構成する。 -/
lemma available_slot_split {m d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d}
    {i : Fin (d + 1)} {v : Fin (m + 1 + d) → Fin (m + 1)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (m + 1 + d))
    (j : Fin (r.val i).val) (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val)
    (k : Fin (m + 1)) (hk : v p = k) :
    ∃ pre post : List {a : Fin (m + 1) // a ≠ k},
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i) = pre.map Subtype.val ++ k :: post.map Subtype.val ∧
        pre.length = j.val := by
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)
  have hn : xs.Nodup := (List.nodup_ofFn_ofInjective (w i).symm.injective).filter _
  have hs : xs = xs.take j.val ++ k :: xs.drop (j.val + 1) := by
    simpa only [hk] using b.available_split p j hp
  have hnd : (xs.take j.val ++ k :: xs.drop (j.val + 1)).Nodup := by rw [← hs]; exact hn
  have hpre : k ∉ xs.take j.val := by
    intro h
    exact (List.nodup_append.mp hnd).2.2 k h k (by simp) rfl
  have hpost : k ∉ xs.drop (j.val + 1) :=
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hpreval := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters_values_of_not_mem k (xs.take j.val) hpre
  have hpostval := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters_values_of_not_mem k (xs.drop (j.val + 1)) hpost
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k (xs.take j.val), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k (xs.drop (j.val + 1)), ?_, ?_⟩
  · rw [hpreval, hpostval]
    exact hs
  · have hj : j.val ≤ xs.length := by
      change j.val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).length
      have := b.bound; have := j.isLt; omega
    simpa only [List.length_map, List.length_take, Nat.min_eq_left hj] using
      congrArg List.length hpreval

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
