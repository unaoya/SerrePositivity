module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SharedOverlapRows

/-!
模型。文献の定義との比較は後で
# 共有端点を持つ全部分語の区間再構成

概要：Berger–Fresse §1.5.8 の重なる部分語を、連結語の縮約の実際の区間へ戻す。
方針：各共有端点で前の一コピーを消し、部分長−1 の累積位置から元の部分語を取り出す。
規約：部分語は非空非退化で、隣接する末尾と先頭が一致する。
使われ方：部分長から構成した OverlapPartition の全 segment を元の部分語へ同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：任意の前半を足した縮約は後半の縮約より短くならない（BF §1.5.8）。
方針：先頭付加は縮約済みの後続文字を消さず、同じ先頭一コピーを省くだけと使う。
規約：二語は空でも退化してもよい。
使われ方：全復元語の長さで任意の部分語の長さを抑える。 -/
lemma collapse_suffix_length_le (pre post : List α) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse post).length ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ post)).length := by
  induction pre with
  | nil => exact Nat.le_refl _
  | cons a pre ih =>
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse post).length ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ post))).length
    apply ih.trans
    cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ post) with
    | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, List.length_nil, List.length_singleton]; omega
    | cons b tail => by_cases hab : a = b <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, hab]

/-- 概要：非退化な全部分語の各長さは全縮約語の長さ以下（BF §1.5.8）。
方針：先頭部分語は縮約の先頭部分保存、後続部分語は後半縮約の長さ単調性を使う。
規約：部分語の非空性・共有端点はこの上界には不要。
使われ方：復元部分長を OverlapPartition の有限値へ包む。 -/
lemma row_length_le_collapse_flatten (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) :
    ∀ row ∈ parts, row.length ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length := by
  induction parts with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons row rest ih =>
    intro word hw
    rcases List.mem_cons.mp hw with rfl | hw
    · have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_prefix word rest.flatten
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self word (hc word List.mem_cons_self)] at hp
      exact hp.length_le
    · exact (ih (fun q hq => hc q (List.mem_cons_of_mem row hq)) word hw).trans
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_suffix_length_le row rest.flatten)

/-- 概要：共有端点で前の末尾一コピーを省くと全縮約語そのものとなる（BF §1.5.8）。
方針：末尾と先頭の同値二コピーを一つにし、残る連結の非退化性を使う。
規約：後続内部は退化してよいが、前半は非空非退化。
使われ方：次の重なり区間へ進むための厳密な語の表示。 -/
lemma collapse_shared_append (row post : List α) (hc : row.IsChain (· ≠ ·))
    (hr : row ≠ []) (hs : row.getLast? = post.head?) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (row ++ post) = row.dropLast ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse post := by
  let a := row.getLast hr
  have ha : row.getLast? = some a := List.getLast?_eq_some_getLast hr
  have hh : post.head? = some a := hs.symm.trans ha
  obtain ⟨tail, hpost⟩ := List.head?_eq_some_iff.mp hh
  have hrow : row.dropLast ++ [a] = row := List.dropLast_append_getLast hr
  have hwords : row ++ post = row.dropLast ++ a :: a :: tail := by
    calc
      _ = (row.dropLast ++ [a]) ++ (a :: tail) := congrArg₂ List.append hrow.symm hpost
      _ = _ := by simp only [List.append_assoc, List.singleton_append]
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (row ++ post) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (row.dropLast ++ post) := by
    rw [hwords, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_duplicate_in_context, hpost]
  have hrc : (row.dropLast ++ [a]).IsChain (· ≠ ·) := by rw [hrow]; exact hc
  have hjoined : (row.dropLast ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse post).IsChain (· ≠ ·) := by
    apply hrc.left_of_append.append (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_isChain post)
    intro b hb c hcm
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_head?, hh] at hcm
    have hec : a = c := Option.mem_some_iff.mp hcm
    subst c
    exact (List.isChain_append.mp hrc).2.2 b hb a rfl
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (row.dropLast ++ post) := he
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (row.dropLast ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse post) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_congr row.dropLast _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_isChain post)).symm
    _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ hjoined

/-- 概要：共有端点を残した次区間は先行部分長−1 だけ進んだ縮約語（BF §1.5.8）。
方針：dropLast と後続の厳密な連結表示から先行部分だけを落とす。
規約：先行部分語は一文字でもよい。
使われ方：各部分語の累積開始位置を帰納的に計算する。 -/
lemma collapse_shared_drop (row post : List α) (hc : row.IsChain (· ≠ ·))
    (hr : row ≠ []) (hs : row.getLast? = post.head?) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (row ++ post)).drop (row.length - 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse post := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_shared_append row post hc hr hs, ← List.length_dropLast, List.drop_left]

/-- 概要：共有端点を持つ全部分語は累積部分長−1 の位置の区間に一致する（BF §1.5.8）。
方針：第零区間は先頭部分保存、後続は共有端点を残す drop で一つずつ進める。
規約：部分語列の任意の実在添字に適用する。
使われ方：復元分割の全 segments を元の部分語列へ同定する。 -/
lemma shared_rows_take (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ [])
    (hs : parts.IsChain (fun row post => row.getLast? = post.head?)) :
    ∀ i (hi : i < parts.length),
      List.take (parts[i]).length
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).drop ((parts.map (fun row => row.length - 1)).take i).sum) =
          parts[i] := by
  induction parts with
  | nil => intro i hi; simp only [List.length_nil] at hi; omega
  | cons row rest ih =>
    intro i hi
    cases i with
    | zero =>
      have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_prefix row rest.flatten
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self row (hc row List.mem_cons_self)] at hp
      obtain ⟨tail, he⟩ := hp
      simp only [List.take_zero, List.sum_nil, List.drop_zero, List.getElem_cons_zero,
        List.flatten_cons, ← he, List.take_left]
    | succ i =>
      have hi' : i < rest.length := by simp only [List.length_cons] at hi; omega
      have hrest : rest ≠ [] := by intro he; simp only [he, List.length_nil] at hi'; omega
      have hcTail : ∀ word ∈ rest, word.IsChain (· ≠ ·) :=
        fun word hw => hc word (List.mem_cons_of_mem row hw)
      have hnTail : ∀ word ∈ rest, word ≠ [] :=
        fun word hw => hne word (List.mem_cons_of_mem row hw)
      have hshare : row.getLast? = rest.flatten.head? := by
        cases rest with
        | nil => exact (hrest rfl).elim
        | cons next rest =>
          rw [List.flatten_cons, List.head?_append_of_ne_nil _ (hnTail next List.mem_cons_self)]
          exact (List.isChain_cons_cons.mp hs).1
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons, List.getElem_cons_succ,
        List.flatten_cons, ← List.drop_drop]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_shared_drop row rest.flatten (hc row List.mem_cons_self)
        (hne row List.mem_cons_self) hshare]
      exact ih hcTail hnTail hs.tail i hi'

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
