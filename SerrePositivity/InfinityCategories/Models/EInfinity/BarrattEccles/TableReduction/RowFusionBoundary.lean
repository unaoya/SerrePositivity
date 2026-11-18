module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusionContext

/-!
模型。文献の定義との比較は後で
# 二つのブロックの共有境界行を直接融合する

概要：Berger–Fresse §1.5.7 の成分境界の行一致を、そのまま実際の全表の融合へ渡す。
方針：左の最終行と右の先頭行を分離し、任意の先行部分での既存の融合定理を適用する。
規約：行長は r+s−1、共有出力は前のコピー一つを削除する。
使われ方：水平・垂直ブロックの連結表から共有頂点を一つだけ持つ表を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*}

/-- 概要：二つのブロックの境界行を一つへ融合する実際の行列（BF §1.5.7）。
方針：左末尾の行を保ち、二つの選択長さから重複する一文字を引く。
規約：どちらかが空なら通常の連結。
使われ方：全成分の共有行を順次融合する演算。 -/
def fuseBoundary (left right : List (List α × ℕ)) : List (List α × ℕ) :=
  match left.getLast?, right with
  | some (row, r), (_, s) :: rest => left.dropLast ++ (row, r + s - 1) :: rest
  | _, _ => left ++ right

/-- 概要：左ブロックの共有出力文字の位置（BF §1.5.7）。
方針：最終行以前の選択長さの和に最終行内の末尾位置を足す。
規約：自然数の切り捨て減算は最終行長にだけ適用する。
使われ方：境界行融合による出力の一文字削除。 -/
def boundaryEraseIndex (left : List (List α × ℕ)) : ℕ :=
  (left.dropLast.map Prod.snd).sum + ((left.getLast?.map Prod.snd).getD 0 - 1)

/-- 概要：行を共有する二つの非空ブロックを任意の全表の中で融合（BF §1.5.7）。
方針：左最終行と右先頭行の一致で既存の局所融合を適用する。
規約：非重複条件は実際の左行にだけ要求する。
使われ方：全成分連結表の実際の成功から共有境界を一つずつ消す。 -/
lemma fuseBoundary_in_context [DecidableEq α] (before left right rest : List (List α × ℕ))
    (initial out : List α) (hl : left ≠ []) (hr : right ≠ [])
    (hn : ∀ row ∈ left.map Prod.fst, row.Nodup)
    (hj : (left.map Prod.fst).getLast? = (right.map Prod.fst).head?)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ left ++ right ++ rest) initial = some out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary left right ++ rest) initial =
      some (out.eraseIdx ((before.map Prod.snd).sum + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex left)) := by
  have hs : ∃ pre row r, left = pre ++ [(row, r)] := by
    obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hl)
    exact ⟨pre, (left.getLast hl).1, (left.getLast hl).2, he⟩
  obtain ⟨pre, row, r, rfl⟩ := hs
  cases right with
  | nil => exact (hr rfl).elim
  | cons p tail =>
    obtain ⟨other, s⟩ := p
    have he : row = other := by simpa using hj
    subst other
    have hnodup : row.Nodup := hn row (by simp)
    have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowFusion_in_context (before ++ pre) initial row hnodup r s (tail ++ rest) out
      (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using h)
    simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex, List.append_assoc, List.map_append,
      List.sum_append, Nat.add_assoc] using hf

/-- 概要：境界融合は左ブロックの先頭行を保つ（BF §1.5.7）。
方針：左末尾を分離し、残る先行行の有無で場合分けする。
規約：両ブロックは非空。
使われ方：融合済みの後続表と前の垂直ブロックを接続する。 -/
lemma fuseBoundary_head (left right : List (List α × ℕ)) (hl : left ≠ []) (hr : right ≠ []) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary left right).map Prod.fst).head? = (left.map Prod.fst).head? := by
  have hs : ∃ pre row r, left = pre ++ [(row, r)] := by
    obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hl)
    exact ⟨pre, (left.getLast hl).1, (left.getLast hl).2, he⟩
  obtain ⟨pre, row, r, rfl⟩ := hs
  cases right with
  | nil => exact (hr rfl).elim
  | cons p tail =>
    obtain ⟨other, s⟩ := p
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary, List.getLast?_concat, List.dropLast_concat]
    cases pre <;> rfl

/-- 概要：境界融合した二つの非空ブロックは非空（BF §1.5.7）。
方針：保存される左先頭行が存在することを使う。
規約：選択長さの正性は不要。
使われ方：融合を繰り返す際の後続表の非空性。 -/
lemma fuseBoundary_ne_nil (left right : List (List α × ℕ)) (hl : left ≠ []) (hr : right ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary left right ≠ [] := by
  intro he
  have hh := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_head left right hl hr
  rw [he] at hh
  have hn : (left.map Prod.fst).head? = none := hh.symm
  have := List.head?_eq_none_iff.mp hn
  exact hl (List.map_eq_nil_iff.mp this)

/-- 概要：成功した非空ブロックの境界削除位置は出力の最終位置（BF §1.5.7）。
方針：実際の最終行長の正性と出力長＝選択長総和を使う。
規約：先行行の長さへ切り捨て減算を移す際は最終行長が正。
使われ方：融合出力を共有文字を一つ消した成分語へ同定する。 -/
lemma boundaryEraseIndex_of_success [DecidableEq α] (left : List (List α × ℕ))
    (initial out : List α) (hl : left ≠ []) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows left initial = some out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex left = out.length - 1 := by
  have hs : ∃ pre row r, left = pre ++ [(row, r)] := by
    obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hl)
    exact ⟨pre, (left.getLast hl).1, (left.getLast hl).2, he⟩
  obtain ⟨pre, row, r, rfl⟩ := hs
  obtain ⟨picked, removed, tail, _, ht, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows pre [(row, r)] initial out h
  have hr := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success row r [] removed tail ht).1
  have hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_length (pre ++ [(row, r)]) initial out h
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero] at hlen
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex, List.dropLast_concat, List.getLast?_concat, Option.map_some,
    Option.getD_some]
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
