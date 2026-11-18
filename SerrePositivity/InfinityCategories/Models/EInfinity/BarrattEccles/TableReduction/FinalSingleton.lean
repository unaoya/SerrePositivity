module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowEndCoefficients
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentDeletionSigns

/-!
模型。文献の定義との比較は後で
# 最終一文字行を持つ退化 table の末尾

概要：Berger–Fresse §1.4.4 の頂点境界に必要な最終一文字行の符号を扱う。
方針：直前の行末の再出現を使って末尾の隣接重複を導き、削除係数を反転する。
規約：退化出力も削除和の途中では捨てない。
使われ方：最終頂点を削除する項の交代符号を保証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：後続行だけに制限しても行末の再出現は保たれる（BF §1.4.4）。
方針：先行行について帰納し、再帰条件の後半を取る。
規約：先行行と後続行は任意のリスト。
使われ方：最終二行の再出現条件を取り出す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds.append_right {α : Type*}
    (before rest : List (List α)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds (before ++ rest)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds rest := by
  induction before with
  | nil => exact h
  | cons row before ih => exact ih h.2

/-- 概要：最終一文字行は直前の行末と同じ文字（BF §1.4.4）。
方針：直前行末の再出現先は最後の一文字しかない。
規約：直前行は非空。
使われ方：出力の最後の二文字が隣接重複することを示す。 -/
lemma recurrentEnds_final_singleton {α : Type*}
    (before : List (List α)) (row : List α) (a : α) (hr : row ≠ [])
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds (before ++ [row, [a]])) : row.getLast hr = a := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds.append_right before [row, [a]] h
  have hm := ht.1 hr (by simp)
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_singleton] using hm

/-- 概要：最終一文字行の直前行末の位置（BF §1.4.4）。
方針：先行行で帰納して位置の移動を加える。
規約：全先行行と直前行は非空。
使われ方：末尾重複の前の削除係数を行番号から読む。 -/
lemma rowEndPositions_before_final_singleton {α : Type*} (before : List (List α))
    (row : List α) (a : α) (hn : ∀ r ∈ before, r ≠ []) (hr : row ≠ []) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions (before ++ [row, [a]]))[before.length]? =
      some (before.flatten.length + row.length - 1) := by
  induction before with
  | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions]
  | cons first before ih =>
    have hp : 0 < first.length := List.length_pos_iff.mpr (hn first (by simp))
    have hs : ∀ r ∈ before, r ≠ [] := fun r hm => hn r (by simp [hm])
    have hpos : 0 < before.flatten.length + row.length := by
      have := List.length_pos_iff.mpr hr
      omega
    cases hb : before ++ [row, [a]] with
    | nil => have := congrArg List.length hb; simp at this
    | cons next rest =>
      have he := ih hs
      rw [hb] at he
      simp only [List.cons_append, hb, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.length_cons,
        List.getElem?_cons_succ, List.getElem?_map, he, Option.map_some,
        List.flatten_cons, List.length_append]
      congr 1
      omega

/-- 概要：最終一文字行を持つ出力の最後の二文字は同値（BF §1.4.4）。
方針：直前行を末尾とそれ以外に分け、再出現条件を代入する。
規約：出力の全射性・非退化性は要求しない。
使われ方：隣接削除の逆符号公式を最終頂点境界へ適用する。 -/
lemma flatten_final_singleton {α : Type*}
    (before : List (List α)) (row : List α) (a : α) (hr : row ≠ [])
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds (before ++ [row, [a]])) :
    (before ++ [row, [a]]).flatten = (before.flatten ++ row.dropLast) ++ [a, a] := by
  have he := List.dropLast_append_getLast hr
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_final_singleton before row a hr h] at he
  calc
    _ = before.flatten ++ (row ++ [a]) := by simp
    _ = before.flatten ++ ((row.dropLast ++ [a]) ++ [a]) := by rw [he]
    _ = _ := by simp only [List.append_assoc, List.singleton_append]

/-- 概要：最終一文字行の削除係数は最後の頂点境界の符号（BF §1.4.4）。
方針：直前行末の係数を計算し、最後の同値の削除係数を反転する。
規約：最終行以外に少なくとも一行がある。
使われ方：退化 table に現れる最終頂点境界項の符号を保存する。 -/
lemma deletionCoefficient_final_singleton {n : ℕ} (before : List (List (Fin n)))
    (row : List (Fin n)) (a : Fin n) (hr : row ≠ [])
    (hn : ∀ r ∈ before, r ≠ []) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds (before ++ [row, [a]]))
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows (before ++ [row, [a]]))
    (out : List (Fin n)) (he : (before ++ [row, [a]]).flatten = out)
    (k : Fin out.length) (hk : k.val + 1 = out.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
      (-1 : ℤ) ^ (before.length + 1) := by
  have hp : 0 < row.length := List.length_pos_iff.mpr hr
  have hlen : out.length = before.flatten.length + row.length + 1 := by
    rw [← he]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_append, List.length_cons, List.length_nil]
    omega
  let j : Fin out.length := ⟨before.flatten.length + row.length - 1, by omega⟩
  have hne : ∀ r ∈ before ++ [row, [a]], r ≠ [] := by
    intro r hm
    rcases List.mem_append.mp hm with hb | hb
    · exact hn r hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hr
      · simp
  have hrep := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.repeatPositions_flatten_eq_rowEnds _ hs hc hne
  have hcoeff := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_raw_rowEnd (fun t : Fin out.length => out[t.val])
    _ hne (by simpa only [List.ofFn_getElem, he] using hrep) before.length j
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_before_final_singleton before row a hn hr)
  have hsplit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.flatten_final_singleton before row a hr hc
  have hjk : j.val + 1 = k.val := by dsimp only [j]; omega
  have hval : out[j.val] = out[k.val] := by
    have ho : out = (before.flatten ++ row.dropLast) ++ [a, a] := he.symm.trans hsplit
    have hlpre : (before.flatten ++ row.dropLast).length = j.val := by
      simp only [List.length_append, List.length_dropLast]
      dsimp only [j]
      omega
    have hkpre : k.val = (before.flatten ++ row.dropLast).length + 1 := by omega
    have hjopt : out[(before.flatten ++ row.dropLast).length]? = some a := by
      rw [ho]
      simp
    have hkopt : out[(before.flatten ++ row.dropLast).length + 1]? = some a := by
      rw [ho, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      rfl
    have hjval : out[j.val] = a := by
      rw [hlpre, List.getElem?_eq_getElem j.isLt] at hjopt
      exact Option.some.inj hjopt
    have hkval : out[k.val] = a := by
      rw [← hkpre, List.getElem?_eq_getElem k.isLt] at hkopt
      exact Option.some.inj hkopt
    exact hjval.trans hkval.symm
  have ha := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_adjacent_eq
    (fun t : Fin out.length => out[t.val]) j k hjk hval
  calc
    _ = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun t : Fin out.length => out[t.val]) j := ha
    _ = _ := by rw [hcoeff, pow_succ]; ring

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
