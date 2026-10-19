module

public import SerrePositivity.EInfinity.TableReduction.BlockBoundary

/-!
# 中央ブロックで終えた抽出の次行の先頭

概要：Berger–Fresse §1.5.8 の垂直連続行で、次行の先頭も内側にあることを示す。
方針：前行の外側前半は全て除外され、末尾の内側文字は次行にも残る。
規約：次行の中央ブロックの並び順は任意。前行の末尾だけを除外せず残す。
使われ方：垂直成分の語を一つの内側区間として復元する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：中央で終えた非重複行の次行の可用先頭も中央に属する（BF §1.5.8）。
方針：切断位置で中央を分け、除外後の前半が空で中央が非空と示す。
規約：前行の末尾 a と次行の先頭 b は実際の可用行の評価で指定する。
使われ方：固定外側頂点の垂直成分で最初以外の行の内側先頭を得る。 -/
lemma available_block_next_head_mem_middle (pre middle middle' post : List α)
    (hm : ∀ x, x ∈ middle' ↔ x ∈ middle) (hn : (pre ++ middle ++ post).Nodup)
    (removed : List α) (a b : α) (r : ℕ) (hr : 0 < r)
    (he : (available removed (pre ++ middle ++ post))[r - 1]? = some a)
    (ha : a ∈ middle)
    (hb : (available
      (removed ++ (available removed (pre ++ middle ++ post)).take (r - 1))
      (pre ++ middle' ++ post)).head? = some b) : b ∈ middle' := by
  obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp ha
  have hs : pre ++ middle ++ post = (pre ++ left) ++ a :: (right ++ post) := by
    simp only [hsplit, List.append_assoc, List.cons_append]
  have hn' : ((pre ++ left) ++ a :: (right ++ post)).Nodup := hs ▸ hn
  have hlen := available_endpoint_prefix_length (pre ++ left) (right ++ post)
    removed a hn' r hr (hs ▸ he)
  have har : a ∉ removed := by
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_getElem? he)).2
  have han : a ∉ pre ++ left := by
    intro hmem
    exact (List.nodup_append.mp hn').2.2 a hmem a (by simp) rfl
  have htake : (available removed (pre ++ middle ++ post)).take (r - 1) =
      available removed (pre ++ left) := by
    rw [hs, hlen, Nat.add_sub_cancel]
    have hav : available removed ((pre ++ left) ++ a :: (right ++ post)) =
        available removed (pre ++ left) ++ a :: available removed (right ++ post) := by
      simp only [available, List.filter_append, List.filter_cons,
        decide_eq_true har, ite_true]
    rw [hav, List.take_left]
  rw [htake] at hb
  let rem := removed ++ available removed (pre ++ left)
  have hpre : available rem pre = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    by_cases hxrem : x ∈ removed <;> simp [rem, available, hxrem, hx]
  have ham : a ∈ available rem middle' := by
    have ham' := (hm a).mpr ha
    simp only [available, List.mem_filter, decide_eq_true_eq]
    exact ⟨ham', by
      simp only [rem, List.mem_append, not_or]
      exact ⟨har, fun h => han (List.mem_of_mem_filter h)⟩⟩
  have hav : available rem (pre ++ middle' ++ post) =
      available rem pre ++ available rem middle' ++ available rem post := by
    simp only [available, List.filter_append]
  change (available rem (pre ++ middle' ++ post)).head? = some b at hb
  rw [hav, hpre, List.nil_append] at hb
  cases hmid : available rem middle' with
  | nil => simp only [hmid, List.not_mem_nil] at ham
  | cons c cs =>
    simp only [hmid, List.cons_append, List.head?_cons, Option.some.injEq] at hb
    subst c
    have hbm : b ∈ available rem middle' := by rw [hmid]; exact List.mem_cons_self
    exact (List.mem_filter.mp hbm).1

end SerrePositivity.EInfinity.TableReduction
