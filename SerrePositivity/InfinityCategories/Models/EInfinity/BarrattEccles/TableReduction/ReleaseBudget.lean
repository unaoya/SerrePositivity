module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearchProperties
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferBounds

/-!
模型。文献の定義との比較は後で
# 実際の Schedule の後続行の逆探索の予算

概要：Berger–Fresse §1.4.4 の探索の長さ条件を元の Schedule の総和から導く。
方針：先行抽出の除外長と、一文字を解放した二状態の長さを比較する。
規約：後続抽出と状態の関係は実際の reduceRows のものを使う。
使われ方：行末側の逆構成から最初に延長する後続行の存在を得る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：全行の長さ−1 のリスト和に 1 を足すと arity（BF §1.4.4）。
方針：有限型の Schedule の総和を行リストの和に移す。
規約：nullary に Schedule がない場合も一般の含意として扱う。
使われ方：先行行と後続行で除外予算を分配する。 -/
lemma rows_excess_sum {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map (fun p => p.2 - 1)).sum + 1 = n := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, List.sum_ofFn, Function.comp_def] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_excess_sum r

/-- 概要：一行の後で一文字を解放すると後続列の探索予算が成立（BF §1.4.4）。
方針：元の総和を前・現在行・後に分け、状態の長さを代入する。
規約：解放前の状態は解放後の状態に一文字を加えたリスト。
使われ方：逆探索の抽象的な予算条件を元の Schedule から確保する。 -/
lemma released_suffix_budget {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (before after : List (List (Fin n) × ℕ))
    (row : List (Fin n)) (s : ℕ) (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ (row, s) :: after)
    (picked : List (List (Fin n))) (removed free : List (Fin n)) (a : Fin n)
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before [] picked removed)
    (hb : s ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
    (hs : removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (s - 1) = free ++ [a]) :
    free.length + 1 + (after.map (fun p => p.2 - 1)).sum + 1 = n := by
  have htotal := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_excess_sum w r
  rw [he] at htotal
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at htotal
  have hprefix := hp.finish_length
  simp only [List.length_nil, Nat.zero_add] at hprefix
  have hstate := congrArg List.length hs
  have hle : s - 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := Nat.le_trans (Nat.sub_le s 1) hb
  simp only [List.length_append, List.length_take, Nat.min_eq_left hle,
    List.length_singleton] at hstate
  omega

/-- 概要：非最終行で一文字を解放した後の実際の列には一意な探索候補が存在（BF §1.4.4）。
方針：元の Schedule の完全行条件・非空の後続列・除外予算を探索の存在証明へ渡す。
規約：解放後の重複のなさと解放値の不所属は呼び出し側の行の短縮から得る。
使われ方：行末削除の逆構成で延長する後続行の存在を適用する。 -/
lemma releaseSearch_on_schedule_suffix {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d)
    (before after : List (List (Fin n) × ℕ))
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) :: after)
    (hi : before.length = i.val) (picked : List (List (Fin n)))
    (removed free : List (Fin n)) (a : Fin n)
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before [] picked removed)
    (hb : (r.val i.castSucc).val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc)).length)
    (hs : removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc)).take
      ((r.val i.castSucc).val - 1) = free ++ [a])
    (hn : free.Nodup) (ha : a ∉ free) (tail : List (Fin n))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows after (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc)).take
      ((r.val i.castSucc).val - 1)) = some tail) :
    ∃ earlier selected finish chosen later,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a after free earlier selected finish chosen later ∧
      finish.Nodup ∧ a ∉ finish ∧
      ∃ suffix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (chosen :: later) (finish ++ [a]) = some suffix := by
  have hnonempty : after ≠ [] := by
    intro hnil
    have hl := congrArg List.length he
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, List.length_append, List.length_cons, hnil,
      List.length_nil] at hl
    have hb := i.isLt
    omega
  have hcomplete : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows after := by
    intro p hmem
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.completeRows_rows w r p
    rw [he]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hmem)
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows after (free ++ [a]) = some tail := by rw [← hs]; exact ht
  have hbudget := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.released_suffix_budget w r before after _ _ he picked removed free a hp hb hs
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.releaseSearch_exists after free a tail hnonempty hcomplete hn ha hsuccess hbudget

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
