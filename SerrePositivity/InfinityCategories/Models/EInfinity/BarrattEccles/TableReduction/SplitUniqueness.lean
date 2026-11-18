module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BlockCoordinates

/-!
模型。文献の定義との比較は後で
# 行位置で指定した分割の一意性

概要：Berger–Fresse §1.4.4 の二つの抽出証明書の先行部分を揃える。
方針：先行行数で take と drop を評価し、証跡の一意性を使う。
規約：行そのものに重複があってもよい。
使われ方：順方向と逆方向の同じ行直前の状態を厳密に同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：同じ長さで切った先行部分と残りは一致（BF §1.4.4）。
方針：等しい連結に take と drop を適用する。
規約：切断位置は先行部分の長さだけで指定する。
使われ方：同じ行番号の前の二つの行分割を一致させる。 -/
lemma split_unique_of_length {α : Type*} (before rest before' rest' : List α)
    (he : before ++ rest = before' ++ rest') (hl : before.length = before'.length) :
    before = before' ∧ rest = rest' := by
  have hp := congrArg (fun xs => xs.take before.length) he
  have ht := congrArg (fun xs => xs.drop before.length) he
  rw [hl] at hp ht
  simp only [← hl, List.take_append_length, List.drop_append_length] at hp ht
  have hp' : before = before' := by
    simpa only [hl, List.take_append_length] using hp
  exact ⟨hp', List.append_cancel_left (hp' ▸ he)⟩

/-- 概要：既存の先行抽出後の指定行の値を全出力位置で読む（BF §1.4.4）。
方針：成功を証跡の終端状態で分け、一行の選択語の添字を照合する。
規約：位置は先行出力長と行内添字で指定する。
使われ方：順方向の相手の解放値が元の削除値に一致することを示す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.value_in_next_row {α : Type*} [DecidableEq α]
    {before : List (List α × ℕ)} {removed finish : List α} {picked : List (List α)}
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish) (row : List α) (r : ℕ)
    (rest : List (List α × ℕ)) (out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (row, r) :: rest) removed = some out)
    (k : Fin out.length) (j : ℕ) (hj : j < r)
    (hk : k.val = picked.flatten.length + j) :
    ∃ hb : j < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish row).length, out[k.val] = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish row)[j] := by
  obtain ⟨tail, ht, hout⟩ := hp.split_success _ _ h
  obtain ⟨_, hbound, post, _, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  have hb : j < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish row).length := by omega
  have hs : out = picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish row).take r ++ post) := by
    rw [hout, he]
  have hlen : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish row).take r).length = r := List.length_take_of_le hbound
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out picked.flatten ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish row).take r)
    post hs k ⟨j, by omega⟩ (by exact hk)
  exact ⟨hb, hv.trans List.getElem_take⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
