module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RecoveredExclusions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeOuterRecovery

/-!
模型。文献の定義との比較は後で
# 任意の可用合成行から元の外側行を復元

概要：Berger–Fresse §1.5.8 の合成可用行の外側射影と連続重複の縮約を計算する。
方針：復元状態の代入表示に、指定値の有無に応じた外側語の復元公式を適用する。
規約：内側 arity 零と全内側文字の除外後も含み、元の除外状態は任意。
使われ方：垂直成分間の外側抽出と元の外側成功表を逆構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定値を含まない語は代入後の外側射影でそのまま戻る（BF §1.5.8）。
方針：各文字で外側ラベルの分岐だけを通過し、元のラベルへ戻す。
規約：内側部分語列は空でも余分でもよい。
使われ方：指定値が最終除外済みの可用外側行を復元する。 -/
lemma outerLabel_substitute_absent {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (hk : k ∉ xs) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : a ≠ k := fun h => hk (h ▸ List.mem_cons_self)
    have ht : k ∉ xs := fun h => hk (List.mem_cons_of_mem a h)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_remaining, ih ht]

/-- 概要：復元外側で指定値が可用なら元の可用内側行は非空（BF §1.5.8）。
方針：内側行が空なら各内側値が除外済みとなり、指定値も除外済みとなる。
規約：内側 arity 零では指定値が可用という仮定自体が成立しない。
使われ方：可用合成行の内側ブロックを指定値一文字へ縮約する。 -/
lemma inner_available_ne_nil_of_slot_available {m n : ℕ} (k : Fin (m + 1))
    (τ : Equiv.Perm (Fin n)) (removed : List (Fin (m + n)))
    (hk : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm) ≠ [] := by
  intro he
  apply hk
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerRemoved_slot k removed).mpr
  intro b
  have hb := List.filter_eq_nil_iff.mp he b
    (List.mem_ofFn.mpr ⟨τ b, τ.symm_apply_apply b⟩)
  have hm : b ∈ removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) := by
    simpa only [decide_eq_true_eq, not_not] using hb
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_innerRemoved k removed b).mp hm

/-- 概要：任意の可用合成行の外側射影を縮めると復元した可用外側行（BF §1.5.8）。
方針：任意の除外の代入表示を使い、指定値があれば非空内側を縮め、なければ通過する。
規約：外側行の順序を保ち、指定値の消滅は全内側除外と一致する。
使われ方：外側行長と成分間の共有端点を実際の合成表から復元する。 -/
lemma outerLabel_available_composition_row {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)).map
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recovered_available_substitute]
  have hn : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm)).Nodup :=
    (List.nodup_ofFn_ofInjective σ.symm.injective).filter _
  have hc := List.Pairwise.isChain hn
  by_cases hk : k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed
  · have ha : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm) := by
      intro h
      exact (of_decide_eq_true (List.mem_filter.mp h).2) hk
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_substitute_absent k _ _ ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ hc]
  · have hm : k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm) :=
      List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨σ k, σ.symm_apply_apply k⟩,
        decide_eq_true hk⟩
    have hcount : [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm)].length =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm)).count k := by
      rw [List.length_singleton, List.count_eq_one_of_mem hn hm]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_outer_substitute k _ _ hcount]
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ hc
    · intro part hp
      have he := List.mem_singleton.mp hp
      subst part
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.inner_available_ne_nil_of_slot_available k τ removed hk

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
