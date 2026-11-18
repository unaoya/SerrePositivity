module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseBudget

/-!
模型。文献の定義との比較は後で
# 非最終行で切った実際の成功抽出

概要：Berger–Fresse §1.4.4 の行末削除の逆ブロックに渡す元の状態を構成する。
方針：指定行より前を分離し、除外状態・後続の完全行・非空性・予算を元の Schedule から得る。
規約：非最終行を Fin d で指定する。
使われ方：逆の抽出へ追加の成功仮定や計数仮定を要求せず接続する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定した非最終行の前後の抽出と計数の証明書（BF §1.4.4）。
方針：先行証跡と現在行以降の成功を同時に保持する。
規約：全ての状態と出力は元の reduceRows のもの。
使われ方：逆ブロックを一般の Schedule の非最終行末へ適用する。 -/
structure NonfinalRowPrefix {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d) (out : List (Fin n)) where
  before : List (List (Fin n) × ℕ)
  after : List (List (Fin n) × ℕ)
  picked : List (List (Fin n))
  removed : List (Fin n)
  localOut : List (Fin n)
  split : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) :: after
  before_length : before.length = i.val
  trace : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before [] picked removed
  success : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) :: after) removed =
    some localOut
  output_eq : out = picked.flatten ++ localOut
  prefix_length : picked.flatten.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.castSucc
  removed_nodup : removed.Nodup
  after_complete : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows after
  after_nonempty : after ≠ []
  budget : removed.length + ((r.val i.castSucc).val - 1) +
    (after.map (fun p => p.2 - 1)).sum + 1 = n

/-- 概要：任意の成功 table の指定した非最終行の証明書を構成（BF §1.4.4）。
方針：行リストを take と drop で分け、既存の先行抽出と除外計数を使う。
規約：出力の非退化性は要求しない。
使われ方：残余の区切り削除の逆構成へ元の全条件を供給する。 -/
lemma nonfinalRowPrefix_nonempty {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NonfinalRowPrefix w r i out) := by
  have hib : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).length := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn]
    have := i.isLt
    omega
  let before := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take i.val
  let after := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 1)
  have hget : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r)[i.val] = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) := by
    change (List.ofFn (fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j, (r.val j).val)))[i.val] = _
    rw [List.getElem_ofFn]
    exact congrArg (fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j, (r.val j).val)) (Fin.ext rfl)
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) :: after := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take i.val ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop i.val := (List.take_append_drop i.val _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hib, hget]
  have hbefore : before.length = i.val := by
    simp only [before, List.length_take, Nat.min_eq_left (Nat.le_of_lt hib)]
  have hsrc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) :: after)
      [] = some out := by rw [← he]; exact h
  obtain ⟨picked, removed, localOut, hp, hs, hout⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows before _ [] out hsrc
  have hlen := hp.output_length
  have hsum := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w r before _ he i.castSucc hbefore
  have hprefix : picked.flatten.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.castSucc := hlen.trans hsum
  have hn : removed.Nodup := hp.finish_nodup (by simp) (by
    intro p hmem
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w r p
    rw [he]
    exact List.mem_append_left _ hmem)
  have hcomplete : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows after := by
    intro p hmem
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.completeRows_rows w r p
    rw [he]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hmem)
  have hnonempty : after ≠ [] := by
    intro hnil
    have hl := congrArg List.length he
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, List.length_append, List.length_cons,
      hnil, List.length_nil] at hl
    have := i.isLt
    omega
  have htotal := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_excess_sum w r
  rw [he] at htotal
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at htotal
  have hcount := hp.finish_length
  simp only [List.length_nil, Nat.zero_add] at hcount
  refine ⟨⟨before, after, picked, removed, localOut, he, hbefore, hp, hs, hout,
    hprefix, hn, hcomplete, hnonempty, ?_⟩⟩
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
