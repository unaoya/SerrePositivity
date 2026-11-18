module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ParsedSubstitution

/-!
模型。文献の定義との比較は後で
# 任意の非退化出力の splitParts と全代入一致

概要：Berger–Fresse §1.5.8–9 の全分割部分語を任意の非退化合成出力から復元する。
方針：非空部分語による代入表示を既存の splitParts の逆公式へ戻し、区間内部の非退化性を移す。
規約：成功 Schedule や元の入力語をこの段階では仮定しない。
使われ方：両復元語長による長さ飽和と、実際の OverlapPartition の逆構成。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：非退化な代入出力の全挿入部分語は内部が非退化（BF §1.5.8）。
方針：外側語で帰納し、各挿入部分語を出力の先頭区間として取り出して射影する。
規約：部分語の非空性や外側語の非退化性は不要。部分語数は指定値の出現回数。
使われ方：一般の splitParts の各区間へ非退化性を供給する。 -/
lemma substitute_parts_isChain {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (hlen : parts.length = xs.count k) (hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).IsChain (· ≠ ·)) :
    ∀ part ∈ parts, part.IsChain (· ≠ ·) := by
  induction xs generalizing parts with
  | nil =>
    have he : parts = [] := List.length_eq_zero_iff.mp (by simpa only [List.count_nil] using hlen)
    subst parts
    simp only [List.not_mem_nil, false_implies, implies_true]
  | cons a xs ih =>
    by_cases ha : a = k
    · subst a
      cases parts with
      | nil => simp only [List.length_nil, List.count_cons_self] at hlen; omega
      | cons part parts =>
        have hl : parts.length = xs.count k := by
          simpa only [List.length_cons, List.count_cons_self, Nat.add_right_cancel_iff] using hlen
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons] at hc
        have hp : part.IsChain (· ≠ ·) :=
          List.isChain_of_isChain_map (insertedPosition m n k)
            (fun a b hab he => hab (congrArg (insertedPosition m n k) he)) hc.left_of_append
        have ht := ih parts hl hc.right_of_append
        intro word hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hp
        · exact ht word hw
    · have hl : parts.length = xs.count k := by simpa [ha] using hlen
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha] at hc
      exact ih parts hl hc.tail

/-- 概要：任意の非退化出力の全復元部分語は正しい個数の非空非退化な代入表示（BF §1.5.8）。
方針：存在する非空部分語表示を splitParts_substitute で一意な実際の計算結果へ同定する。
規約：外側語は合成出力だけからの outerWord。元の入力語や分割は仮定しない。
使われ方：元の内側語への一意な OverlapPartition と合成語一致を構成する。 -/
lemma splitParts_properties {m n : ℕ} (k : Fin (m + 1))
    (out : List (Fin (m + n))) (hc : out.IsChain (· ≠ ·)) :
    let parts := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) out
    parts.length = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).count k ∧
      (∀ part ∈ parts, part ≠ []) ∧ (∀ part ∈ parts, part.IsChain (· ≠ ·)) ∧
      out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) parts := by
  obtain ⟨parts, hlen, hn, hsub⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.exists_nonempty_parts k out hc
  have hx : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).IsChain (· ≠ ·) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_isChain _
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) out = parts :=
    (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out)) hsub).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts_substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) parts hlen hx)
  change _ ∧ _ ∧ _ ∧ _
  rw [he]
  refine ⟨hlen, hn, ?_, hsub⟩
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.substitute_parts_isChain k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) parts hlen
  rwa [← hsub]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
