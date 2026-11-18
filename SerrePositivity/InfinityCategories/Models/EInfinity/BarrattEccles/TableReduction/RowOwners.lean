module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.OccurrenceRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOffsets

/-!
模型。文献の定義との比較は後で
# 成功 table の削除位置の所属行

概要：Berger–Fresse §1.4.4 の削除位置を Schedule の行番号と行内の位置に分ける。
方針：抽出行の分割と、行長リストの証明書から開始位置を計算する。
規約：退化出力も含む。
使われ方：削除行を決め、前の同値の出現がそれより前の行にあることを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：抽出行の先行部分の長さは Schedule の行開始位置（BF §1.4.4）。
方針：行長リストの等式を take と和で評価する。
規約：行番号は先行行数と一致する。
使われ方：平坦化した位置の行内分解を Schedule の位置へ移す。 -/
lemma picked_prefix_length {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (picked before : List (List (Fin n))) (row : List (Fin n))
    (after : List (List (Fin n))) (hs : picked = before ++ row :: after)
    (he : picked.map List.length = List.ofFn (fun j => (r.val j).val))
    (i : Fin (d + 1)) (hi : before.length = i.val) :
    before.flatten.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i := by
  have ht : picked.take before.length = before := by rw [hs]; simp
  have hm : before.map List.length =
      (List.ofFn (fun j => (r.val j).val)).take before.length := by
    calc
      _ = (picked.take before.length).map List.length := by rw [ht]
      _ = (picked.map List.length).take before.length := List.map_take
      _ = _ := by rw [he]
  simpa only [List.length_flatten, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset, hi] using congrArg List.sum hm

/-- 概要：成功 table の任意の削除位置を実際の行と行内添字へ分ける（BF §1.4.4）。
方針：抽出行の平坦化を位置で分割し、行長と開始位置を Schedule に移す。
規約：所属行の重複のなさも同時に保持する。
使われ方：相殺対で長さを減らす行を具体的に指定する。 -/
lemma output_position_owner {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (k : Fin out.length) :
    ∃ (i : Fin (d + 1)) (pre row post : List (Fin n)) (j : Fin row.length),
      out = pre ++ (row ++ post) ∧ row.Nodup ∧ pre.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i ∧
        row.length = (r.val i).val ∧ k.val = pre.length + j.val := by
  obtain ⟨picked, he, hs, hn, hl, hlengths⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.separatedRows_of_reduction w r out h
  have hk : k.val < picked.flatten.length := by rw [he]; exact k.isLt
  obtain ⟨before, row, after, hsplit, j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.flatten_position_decomposition picked k.val hk
  have hb : before.length < picked.length := by rw [hsplit]; simp
  let i : Fin (d + 1) := ⟨before.length, by omega⟩
  have hrow : picked[before.length] = row := by
    have ht : picked[before.length]? = some row := by rw [hsplit]; simp
    rw [List.getElem?_eq_getElem hb] at ht
    exact Option.some.inj ht
  have hrowlength := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.picked_length_at r picked hl hlengths i
  change (picked[before.length]).length = (r.val i).val at hrowlength
  rw [hrow] at hrowlength
  refine ⟨i, before.flatten, row, after.flatten, j, ?_, ?_, ?_, hrowlength, hj⟩
  · calc
      _ = picked.flatten := he.symm
      _ = (before ++ row :: after).flatten := congrArg List.flatten hsplit
      _ = _ := by rw [List.flatten_append, List.flatten_cons]
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows.row_nodup before row after ((congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows hsplit).mp hs)
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.picked_prefix_length r picked before row after hsplit hlengths i rfl

/-- 概要：同じ行内の指定位置は行全体の開始位置を足して評価できる（BF §1.4.4）。
方針：連結リストの要素の右・左の評価を順に適用する。
規約：前後の語は任意。
使われ方：前の同値の出現と削除行の要素を比較する。 -/
lemma getElem_inside_row {α : Type*} (pre row post : List α) (j : Fin row.length) :
    (pre ++ (row ++ post))[pre.length + j.val]'(by
      simp only [List.length_append]; omega) = row[j.val] := by
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem_append_left j.isLt

/-- 概要：所属行内の同じ値の前の出現はその行より前（BF §1.4.4）。
方針：全出力の評価を所属行へ移し、行の単射性を適用する。
規約：前の位置は有限添字で指定する。
使われ方：受け取り行が削除行より前にあることを導く。 -/
lemma previous_position_before_owner {α : Type*} (out pre row post : List α)
    (he : out = pre ++ (row ++ post)) (hn : row.Nodup)
    (k p : Fin out.length) (j : Fin row.length) (hk : k.val = pre.length + j.val)
    (hp : p < k) (hv : out[p.val] = out[k.val]) : p.val < pre.length := by
  have hget : out[k.val] = row[j.val] := by
    refine (List.getElem_of_eq he k.isLt).trans ?_
    simpa only [hk] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_inside_row pre row post j
  have hgetp : (pre ++ (row ++ post))[p.val]'(by
      have := p.isLt; have hlen := congrArg List.length he; omega) = row[j.val] :=
    (List.getElem_of_eq he p.isLt).symm.trans (hv.trans hget)
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.previous_position_lt_row_start pre row post hn j.val p.val j.isLt _ hgetp
  change p.val < k.val at hp
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
