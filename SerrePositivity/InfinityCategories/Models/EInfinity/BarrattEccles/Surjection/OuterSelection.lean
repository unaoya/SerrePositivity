module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapsePrefixes
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterRowProjection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonRows

/-!
模型。文献の定義との比較は後で
# 合成行の選択語と除外更新の外側復元

概要：Berger–Fresse §1.5.8 の合成行の抽出を元の外側行の抽出へ戻す。
方針：外側射影の縮約は先頭部分と共有文字からの後続を保ち、除外集合を決める。
規約：復元除外リストの順序ではなく所属集合を合わせ、後続抽出を移す。
使われ方：元の外側成功表と垂直成分間の接続を合成表から逆構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：外側へ復元した選択語は元の可用外側行の先頭部分（BF §1.5.8）。
方針：縮約の先頭部分保存と可用行の外側復元を組み合わせる。
規約：行長は実際の選択語の外側縮約長。
使われ方：合成の選択長から元の外側選択長と語を得る。 -/
lemma outerSelection_take {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) (r : ℕ) :
    let picked := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm)).take picked.length = picked := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_take_prefix
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)).map
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k)) r
  rw [← List.map_take, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_available_composition_row] at h
  exact h

/-- 概要：成功する合成選択長から正で有効な外側選択長を得る（BF §1.5.8）。
方針：元の選択語の非空性は縮約で保たれ、先頭部分の一致から上限を得る。
規約：元の選択長は正で可用合成行長以下。
使われ方：元の外側行で実際の抽出成功分岐を構成する。 -/
lemma outerSelection_bounds {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) (r : ℕ) (hr : 0 < r)
    (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).length) :
    let picked := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r)
    0 < picked.length ∧ picked.length ≤
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm)).length := by
  have htake := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_take k σ τ removed r
  have hpos : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r) ≠ [] := by
    intro he
    have hnil := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_nil_iff _).mp he
    have ht := List.map_eq_nil_iff.mp hnil
    have hl := congrArg List.length ht
    simp only [List.length_take, Nat.min_eq_left hb, List.length_nil] at hl
    omega
  refine ⟨List.length_pos_iff.mpr hpos, ?_⟩
  have hl := congrArg List.length htake
  simp only [List.length_take] at hl
  omega

/-- 概要：合成の実際の除外更新を外側の選択末尾を残す更新へ復元する（BF §1.5.8）。
方針：同じ行で除外後に残る後続を縮約順位で比較し、全外側値の除外所属を戻す。
規約：両除外リストの順序や重複数ではなく全ての値の所属が一致する。
使われ方：復元した外側抽出を次の合成行の復元状態へ接続する。 -/
lemma outerSelection_update_mem {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) (r : ℕ) (hr : 0 < r)
    (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).length) (a : Fin (m + 1)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
    let picked := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (xs.take r)
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k (removed ++ xs.take (r - 1)) ↔
      a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm)).take (picked.length - 1) := by
  let row := List.ofFn (permutationComposition m n k σ τ).symm
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row
  let picked := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (xs.take r)
  have hi : r - 1 < (xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k)).length := by
    rw [List.length_map]
    change r ≤ xs.length at hb
    omega
  have hdrop := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_drop_rank (xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k)) (r - 1) hi
  have hi' : r - 1 + 1 = r := by omega
  rw [← List.map_drop, ← List.map_take, hi'] at hdrop
  have hold := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_available_composition_row k σ τ removed
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k)) = _ at hold
  rw [hold] at hdrop
  have hsame := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row
    (List.nodup_ofFn_ofInjective (permutationComposition m n k σ τ).symm.injective) (r - 1)
  have hnew := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_available_composition_row k σ τ (removed ++ xs.take (r - 1))
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ xs.take (r - 1)) row).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k)) = _ at hnew
  rw [hsame] at hnew
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k (removed ++ xs.take (r - 1))) (List.ofFn σ.symm) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm)).take (picked.length - 1))
        (List.ofFn σ.symm) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take _ _ (List.nodup_ofFn_ofInjective σ.symm.injective)]
    exact hnew.symm.trans hdrop
  have hm : a ∈ List.ofFn σ.symm := List.mem_ofFn.mpr ⟨σ a, σ.symm_apply_apply a⟩
  have he' : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k (removed ++ xs.take (r - 1))) (List.ofFn σ.symm) ↔
      a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm)).take (picked.length - 1))
        (List.ofFn σ.symm) := by rw [he]
  have hmembership (state : List (Fin (m + 1))) :
      a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available state (List.ofFn σ.symm) ↔ a ∉ state := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.mem_filter, hm, true_and, decide_eq_true_eq]
  rw [hmembership, hmembership] at he'
  simpa only [not_not] using he'.not

/-- 概要：合成一行の成功長から元の外側一行と任意の後続抽出を接続する（BF §1.5.8）。
方針：外側選択語と行長を復元し、除外集合の一致で後続の成功を移す。
規約：後続は次の復元状態で与え、元の除外リストの順序は仮定しない。
使われ方：任意の成功合成表から元の外側表の抽出を逆構成する。 -/
lemma outerSelection_step {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) (r : ℕ) (hr : 0 < r)
    (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).length)
    (rest : List (List (Fin (m + 1)) × ℕ)) (tail : List (Fin (m + 1)))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k (removed ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)).take (r - 1))) =
        some tail) :
    let picked := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r)
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((List.ofFn σ.symm, picked.length) :: rest) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) =
      some (picked ++ tail) := by
  obtain ⟨hr', hb'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_bounds k σ τ removed r hr hb
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_update_mem k σ τ removed r hr hb)
  have ht' := he ▸ ht
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success _ _ _ _ _ hr' hb' ht'
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_take] at hs
  exact hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
