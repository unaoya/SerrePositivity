module

public import SerrePositivity.EInfinity.TableReduction.ScheduleDeletion
public import SerrePositivity.EInfinity.TableReduction.SingletonRows
public import SerrePositivity.EInfinity.Surjection.ListErasure

/-!
# 頂点削除後の table と元の一文字行の削除

概要：Berger–Fresse §1.4.4 の頂点境界の table を実際の行リスト上で比較する。
方針：succAbove による有限列の制限を eraseIdx に直し、抽出の削除補題を適用する。
規約：一文字行は任意の位置にあってよい。
使われ方：頂点境界と削除微分の項の出力一致を証明する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

/-- 概要：有限列の一成分の削除は succAbove による制限（BF §1.4.4）。
方針：削除位置の前後で成分を比較する。
規約：先頭と末尾の削除も含む。
使われ方：頂点を一つ削除した table の行リストを計算する。 -/
lemma ofFn_succAbove_eq_eraseIdx {α : Type*} {m : ℕ} (f : Fin (m + 1) → α)
    (i : Fin (m + 1)) : List.ofFn (fun j => f (i.succAbove j)) =
      (List.ofFn f).eraseIdx i.val := Surjection.ofFn_succAbove_eraseIdx f i

/-- 概要：一文字行を削除した Schedule の table は頂点削除の table（BF §1.4.4）。
方針：ofFn の一成分を除く一般公式を適用する。
規約：置換列からも同じ位置の頂点を除く。
使われ方：抽出の成功を BE の指定した余面へ移す。 -/
lemma rows_scheduleDelete {n d : ℕ} (w : Fin (d + 2) → Equiv.Perm (Fin n))
    (r : Schedule n (d + 1)) (i : Fin (d + 2)) (hi : (r.val i).val = 1) :
    rows (fun j => w (i.succAbove j)) (scheduleDelete r i hi) =
      (rows w r).eraseIdx i.val := by
  exact ofFn_succAbove_eq_eraseIdx
    (fun j => (List.ofFn (fun k => (w j)⁻¹ k), (r.val j).val)) i

/-- 概要：一文字行を除くと出力の指定部分の一文字だけが消える（BF §1.4.4）。
方針：先行行で帰納し、その出力長を指定行長の和として保持する。
規約：除外状態は任意。
使われ方：頂点削除に対応する文字の実際の位置を指定する。 -/
lemma reduceRows_delete_singleton_length {α : Type*} [DecidableEq α]
    (before : List (List α × ℕ)) (row : List α) (rest : List (List α × ℕ))
    (removed out : List α) (h : reduceRows (before ++ (row, 1) :: rest) removed = some out) :
    ∃ pre a post, out = pre ++ a :: post ∧
      pre.length = (before.map Prod.snd).sum ∧
      reduceRows (before ++ rest) removed = some (pre ++ post) := by
  induction before generalizing removed out with
  | nil =>
    obtain ⟨a, tail, ht, he⟩ := reduceRows_singleton_success row rest removed out h
    exact ⟨[], a, tail, he, rfl, ht⟩
  | cons p before ih =>
    obtain ⟨hr, hb, tail, ht, he⟩ := reduceRows_cons_success _ _ _ _ _ h
    obtain ⟨pre, a, post, hp, hl, hc⟩ := ih _ _ ht
    refine ⟨(available removed p.1).take p.2 ++ pre, a, post, ?_, ?_, ?_⟩
    · rw [he, hp, List.append_assoc]
    · simp only [List.length_append, List.length_take, Nat.min_eq_left hb, hl,
        List.map_cons, List.sum_cons]
    · have hs := reduceRows_cons_of_success p.1 p.2 (before ++ rest) removed
        (pre ++ post) hr hb hc
      simpa only [List.cons_append, List.append_assoc] using hs

/-- 概要：成功 table の一文字行を除いた出力と頂点境界の table は一致（BF §1.4.4）。
方針：行リストを指定位置で分割して一文字行削除を適用する。
規約：出力の退化を仮定せず、最後の一文字行も含む。
使われ方：頂点境界の各項へ、出力一致と削除位置を同時に供給する。 -/
lemma reduceRows_deleted_vertex {n d : ℕ} (w : Fin (d + 2) → Equiv.Perm (Fin n))
    (r : Schedule n (d + 1)) (i : Fin (d + 2)) (hi : (r.val i).val = 1)
    (out : List (Fin n)) (h : reduceRows (rows w r) [] = some out) :
    ∃ pre a post, out = pre ++ a :: post ∧
      pre.length = (((List.ofFn (fun j => (r.val j).val)).take i.val).sum) ∧
      reduceRows (rows (fun j => w (i.succAbove j)) (scheduleDelete r i hi)) [] =
        some (pre ++ post) := by
  have hib : i.val < (rows w r).length := by simpa only [rows, List.length_ofFn] using i.isLt
  have he : rows w r = (rows w r).take i.val ++
      (List.ofFn (fun k => (w i)⁻¹ k), 1) :: (rows w r).drop (i.val + 1) := by
    calc
      _ = (rows w r).take i.val ++ (rows w r).drop i.val :=
        (List.take_append_drop i.val (rows w r)).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons hib]
        simp only [rows, List.getElem_ofFn, Fin.eta, hi]
  rw [he] at h
  obtain ⟨pre, a, post, hp, hl, hc⟩ := reduceRows_delete_singleton_length _ _ _ _ _ h
  refine ⟨pre, a, post, hp, ?_, ?_⟩
  · rw [List.map_take, rows, List.map_ofFn] at hl
    exact hl
  · rw [rows_scheduleDelete, List.eraseIdx_eq_take_drop_succ]
    exact hc

end SerrePositivity.EInfinity.TableReduction
