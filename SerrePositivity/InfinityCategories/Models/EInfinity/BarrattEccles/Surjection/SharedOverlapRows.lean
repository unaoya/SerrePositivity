module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CollapseBoundaryLength

/-!
模型。文献の定義との比較は後で
# 長さの飽和から全挿入部分語の共有端点を強制

概要：Berger–Fresse §1.5.8 の逆構成で、復元内側語の長さから重なる分割を検出する。
方針：非退化な各部分語の境界損失は高々一なので、総損失が境界数なら全境界が一致する。
規約：各部分語は非空で内部が非退化。離れた同値の出現は許す。
使われ方：成功 shuffle 出力から取り出す挿入連続区間の全共有端点を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
private lemma flatten_cons_nonempty (row : List α) (rest : List (List α)) (hne : row ≠ []) :
    (row :: rest).flatten ≠ [] := by
  intro he
  have hl := congrArg List.length he
  have hp := List.length_pos_iff.mpr hne
  simp only [List.flatten_cons, List.length_append, List.length_nil] at hl
  omega

/-- 概要：非空非退化な部分語の連結の縮約損失は境界数以下（BF §1.5.8）。
方針：先頭の部分語を足すたびに高々一文字だけを失うことを帰納的に数える。
規約：部分語列全体が空でもよい。
使われ方：復元語長の等式で各境界の損失が最大となることを強制する。 -/
lemma collapse_flatten_length_le (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ []) :
    parts.flatten.length ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length + (parts.length - 1) := by
  induction parts with
  | nil => simp only [List.flatten_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, List.length_nil]; omega
  | cons row rest ih =>
    have hr := hne row List.mem_cons_self
    have hrow := hc row List.mem_cons_self
    have hcTail : ∀ word ∈ rest, word.IsChain (· ≠ ·) :=
      fun word hw => hc word (List.mem_cons_of_mem row hw)
    have hnTail : ∀ word ∈ rest, word ≠ [] :=
      fun word hw => hne word (List.mem_cons_of_mem row hw)
    have hi := ih hcTail hnTail
    cases rest with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
        List.length_nil, Nat.add_sub_cancel, Nat.add_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ hrow]
      exact Nat.le_refl _
    | cons next rest =>
      have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_prepend_length row (next :: rest).flatten hrow hr
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.flatten_cons_nonempty next rest (hnTail next List.mem_cons_self))
      simp only [List.flatten_cons, List.length_append, List.length_cons] at hi hp ⊢
      split_ifs at hp <;> omega

/-- 概要：縮約損失が全境界数に達すれば各隣接部分語は端点を共有する（BF §1.5.8）。
方針：一つでも境界が異なれば総損失が上界より小さくなることを排除して帰納する。
規約：部分語は非空非退化。長さ飽和だけを追加し、端点一致を仮定しない。
使われ方：元の OverlapPartition を実際の合成出力から逆構成する。 -/
lemma shared_endpoints_of_saturated (parts : List (List α))
    (hc : ∀ row ∈ parts, row.IsChain (· ≠ ·)) (hne : ∀ row ∈ parts, row ≠ [])
    (hsat : parts.flatten.length = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse parts.flatten).length + (parts.length - 1)) :
    parts.IsChain (fun pre post => pre.getLast? = post.head?) := by
  induction parts with
  | nil => exact List.isChain_nil
  | cons row rest ih =>
    have hr := hne row List.mem_cons_self
    have hrow := hc row List.mem_cons_self
    have hcTail : ∀ word ∈ rest, word.IsChain (· ≠ ·) :=
      fun word hw => hc word (List.mem_cons_of_mem row hw)
    have hnTail : ∀ word ∈ rest, word ≠ [] :=
      fun word hw => hne word (List.mem_cons_of_mem row hw)
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_prepend_length row (next :: rest).flatten hrow hr
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.flatten_cons_nonempty next rest (hnTail next List.mem_cons_self))
      have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_flatten_length_le (next :: rest) hcTail hnTail
      have he : row.getLast? = (next :: rest).flatten.head? := by
        by_contra he
        rw [ite_eq_right he] at hp
        simp only [List.flatten_cons, List.length_append, List.length_cons] at hsat hb hp
        omega
      have hsatTail : (next :: rest).flatten.length =
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (next :: rest).flatten).length + ((next :: rest).length - 1) := by
        rw [ite_eq_left he] at hp
        simp only [List.flatten_cons, List.length_append, List.length_cons] at hsat hp ⊢
        omega
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, ih hcTail hnTail hsatTail⟩
      rwa [List.flatten_cons, List.head?_append_of_ne_nil _ (hnTail next List.mem_cons_self)] at he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
