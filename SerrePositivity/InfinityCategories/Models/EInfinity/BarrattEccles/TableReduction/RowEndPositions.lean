module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RepeatPositions

/-!
模型。文献の定義との比較は後で
# Table の非最終行末と区切り位置の一致

概要：Berger–Fresse §1.4.4 の削除符号の区切りを実際の table の行末で記述する。
方針：各行内部は最終出現で、非最終行末は後続に再出現することを使う。
規約：行末の自然数位置は出力の先頭から数える。
使われ方：削除位置の区切り順位を行番号へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非最終行の末尾の位置の列（BF §1.4.4）。
方針：最初の行末と、後続の位置を最初の行長だけずらした列を連結する。
規約：最後の行の末尾は含めない。
使われ方：区切りの位置と行番号の対応を指定する。 -/
def rowEndPositions {α : Type*} : List (List α) → List ℕ
  | [] => []
  | [_] => []
  | row :: next :: rest => (row.length - 1) ::
      (rowEndPositions (next :: rest)).map (fun k => row.length + k)

/-- 概要：非最終行末の個数は行数−1（BF §1.4.4）。
方針：行のリストで帰納する。
規約：空の table の値も零。
使われ方：区切りがちょうど d 個であることを行数から読む。 -/
lemma rowEndPositions_length {α : Type*} (picked : List (List α)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).length = picked.length - 1 := by
  induction picked with
  | nil => rfl
  | cons row rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.length_cons, List.length_map, Nat.add_sub_cancel] at ih ⊢
      omega

/-- 概要：分離した再出現行末の語の区切り位置は非最終行末（BF §1.4.4）。
方針：各行の末尾以外を新鮮な先頭として除き、再出現する末尾だけを一つ加える。
規約：全行は非空。
使われ方：table の境界から削除係数の符号を計算する。 -/
lemma repeatPositions_flatten_eq_rowEnds {α : Type*} [DecidableEq α]
    (picked : List (List α)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked →
    (∀ row ∈ picked, row ≠ []) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions picked.flatten = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked := by
  induction picked with
  | nil => intro _ _ _; rfl
  | cons row rest ih =>
    intro hs hc hn
    have hr := hn row (List.mem_cons_self ..)
    have hpos : 0 < row.length := List.length_pos_iff.mpr hr
    have hnrest : ∀ r ∈ rest, r ≠ [] := fun r hm => hn r (List.mem_cons_of_mem _ hm)
    cases rest with
    | nil =>
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions] using
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions_eq_nil_of_nodup row hs.1
    | cons next rest =>
      let a := row.getLast hr
      have hsplit : row.dropLast ++ [a] = row := List.dropLast_append_getLast hr
      have hnd : (row.dropLast ++ [a]).Nodup := by rw [hsplit]; exact hs.1
      have hna : a ∉ row.dropLast := by
        intro ha
        exact (List.nodup_append.mp hnd).2.2 a ha a (by simp) rfl
      have hf : ∀ x ∈ row.dropLast, x ∉ a :: (next :: rest).flatten := by
        intro x hx hy
        rcases List.mem_cons.mp hy with he | ht
        · subst x
          exact hna hx
        · exact hs.2.1 x hx ht
      have he : row ++ (next :: rest).flatten = row.dropLast ++ a :: (next :: rest).flatten := by
        calc
          _ = (row.dropLast ++ [a]) ++ (next :: rest).flatten := by rw [hsplit]
          _ = _ := by rw [List.append_assoc, List.singleton_append]
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (row ++ (next :: rest).flatten) = _
      rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions_fresh_prepend _ _ (List.nodup_append.mp hnd).1 hf]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions, ite_eq_left (hc.1 hr (by simp))]
      rw [ih hs.2.2 hc.2 hnrest]
      simp only [List.map_cons, List.map_map, List.length_dropLast, Nat.add_zero,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions]
      apply congrArg (List.cons (row.length - 1))
      apply congrArg (fun f : ℕ → ℕ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions (next :: rest)).map f)
      funext k
      simp only [Function.comp_apply]
      omega

/-- 概要：成功した TR の区切り位置は実際の非最終行末の列（BF §1.4.4）。
方針：抽出証跡と長さの計数で再出現を強制し、区切り位置の列へ移す。
規約：出力が退化していても成立する。
使われ方：行長の部分和と削除微分の区切り順位を接続する。 -/
lemma rowEnds_of_reduction {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∃ picked, picked.flatten = out ∧ (∀ row ∈ picked, row ≠ []) ∧
      picked.length = d + 1 ∧ picked.map List.length = List.ofFn (fun i => (r.val i).val) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked := by
  obtain ⟨picked, he, hs, hc, hn, hl, hlengths⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_reduction w r out h
  refine ⟨picked, he, hn, hl, hlengths, ?_⟩
  rw [← he]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.repeatPositions_flatten_eq_rowEnds picked hs hc hn

/-- 概要：成功した TR の有限語の Caesura は行末の位置に一致（BF §1.4.4）。
方針：再出現位置と有限語の区切りの同値を適用する。
規約：出力リストの長さの有限添字で評価する。
使われ方：table の行末に実際の deletionCoefficient を適用する。 -/
lemma rowEnds_caesura_iff {n : ℕ} (picked : List (List (Fin n))) (out : List (Fin n))
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked) (i : Fin out.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) i ↔ i.val ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_repeatPositions (fun j : Fin out.length => out[j.val]) i
  simpa only [List.ofFn_getElem, he] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
