module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InnerRowProjection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationStateSubstitution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExclusionEquivalence

/-!
模型。文献の定義との比較は後で
# 任意の合成除外状態から内外の状態を復元

概要：Berger–Fresse §1.5.8 の逆構成で、合成の除外文字から元の内外の除外を定める。
方針：外側の残りラベルはそのまま戻し、全内側文字が除外された場合に指定値を除く。
規約：除外順序は復元せず所属集合を保つ。元のリストには重複を許す。
使われ方：任意の成功合成表の可用行を元の内外の可用行へ逆分解する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：合成除外集合から復元する外側の除外リスト（BF §1.5.8）。
方針：全外側値を列挙し、指定値以外は元の除外、指定値は内側全除外で判定する。
規約：内側 arity 零では指定値は除外済みになる。
使われ方：外側の可用行と選択語を合成表から復元する。 -/
def outerRemoved {m n : ℕ} (k : Fin (m + 1)) (removed : List (Fin (m + n))) :
    List (Fin (m + 1)) :=
  (List.finRange (m + 1)).filter (fun a =>
    if h : a = k then decide (∀ b : Fin n, insertedPosition m n k b ∈ removed)
    else decide (remainingPosition m n k ⟨a, h⟩ ∈ removed))

/-- 概要：残る外側値の復元除外は元の合成除外と一致（BF §1.5.8）。
方針：有限列挙の所属と指定値以外の分岐を計算する。
規約：指定値でない証明を持つ元の外側値。
使われ方：外側ブロックの可用値を復元する。 -/
@[simp] lemma mem_outerRemoved_remaining {m n : ℕ} (k : Fin (m + 1))
    (removed : List (Fin (m + n))) (a : {a : Fin (m + 1) // a ≠ k}) :
    a.val ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed ↔ remainingPosition m n k a ∈ removed := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved, List.mem_filter, List.mem_finRange, true_and,
    dite_eq_right a.property, decide_eq_true_eq]

/-- 概要：指定値の復元除外は全内側文字の元の除外と一致（BF §1.5.8）。
方針：指定値の分岐を計算する。
規約：空の内側 arity での全称条件も含む。
使われ方：内側がまだ可用かどうかを外側の指定値の有無へ移す。 -/
@[simp] lemma mem_outerRemoved_slot {m n : ℕ} (k : Fin (m + 1))
    (removed : List (Fin (m + n))) :
    k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed ↔ ∀ b : Fin n, insertedPosition m n k b ∈ removed := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved]

/-- 概要：内側ラベルの復元除外は元の合成除外と一致（BF §1.5.8）。
方針：内側射影の部分単射性で filterMap の所属を戻す。
規約：内側除外は元の除外リストの内側射影そのもの。
使われ方：復元した二つの状態から合成除外集合を再構成する。 -/
@[simp] lemma mem_innerRemoved {m n : ℕ} (k : Fin (m + 1))
    (removed : List (Fin (m + n))) (b : Fin n) :
    b ∈ removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ↔ insertedPosition m n k b ∈ removed :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_filterMap_of_partial_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k)
    removed (insertedPosition m n k b) b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_inserted k b)

/-- 概要：復元した内外除外状態の合成は元と同じ集合を除外する（BF §1.5.8）。
方針：挿入ラベルの直和分解で外側・内側を分け、全内側除外の条件を吸収する。
規約：除外リスト自身の順序や重複の一致は要求しない。
使われ方：前向きの全段階の行公式を任意の合成表の逆構成へ適用する。 -/
lemma recovered_state_mem {m n : ℕ} (k : Fin (m + 1))
    (removed : List (Fin (m + n))) (a : Fin (m + n)) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) ↔
      a ∈ removed := by
  obtain ⟨z, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.surjective a
  cases z with
  | inl b =>
    change remainingPosition m n k b ∈ _ ↔ remainingPosition m n k b ∈ removed
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_compositionStateRemoved, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerRemoved_remaining]
  | inr b =>
    change insertedPosition m n k b ∈ _ ↔ insertedPosition m n k b ∈ removed
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_compositionStateRemoved, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_innerRemoved, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerRemoved_slot]
    exact ⟨fun h => h.elim id (fun hall => hall b), Or.inl⟩

/-- 概要：正の内側 arity では初期の空除外を空の外側除外へ復元する（BF §1.5.8）。
方針：残る外側値は未除外であり、一つの内側値があるため指定値も未除外となる。
規約：内側 arity 零には適用しない。
使われ方：逆構成で得た外側抽出を元の空の初期状態から開始する。 -/
lemma outerRemoved_nil {m n : ℕ} (k : Fin (m + 1)) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved (n := n) k [] = [] := by
  have hnonempty : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply List.filter_eq_nil_iff.mpr
  intro a _
  by_cases h : a = k <;> simp [h]

/-- 概要：合成除外集合の増加は復元外側除外集合の増加を与える（BF §1.5.8）。
方針：指定値以外は元の包含、指定値は全内側除外の包含を使う。
規約：リストの順序や重複数に関する単調性は要求しない。
使われ方：成分間の外側の除外状態が後戻りしないことを確認する。 -/
lemma outerRemoved_subset {m n : ℕ} (k : Fin (m + 1))
    (removed more : List (Fin (m + n))) (h : removed ⊆ more) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed ⊆ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k more := by
  intro a ha
  by_cases he : a = k
  · subst a
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerRemoved_slot] at ha ⊢
    intro b
    exact h (ha b)
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerRemoved_remaining k more ⟨a, he⟩).mpr
      (h ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_outerRemoved_remaining k removed ⟨a, he⟩).mp ha))

/-- 概要：任意の合成可用行は復元した二つの可用行への代入（BF §1.5.8）。
方針：除外集合の一致で全段階の前向きの行公式を元の除外へ戻す。
規約：元の除外が前向き構成の状態であるという仮定を置かない。
使われ方：外側語の縮約と成分間の状態の一致を合成表の実際の成功へ接続する。 -/
lemma recovered_available_substitute {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) (List.ofFn σ.symm))
        [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm)] := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_congr_removed _ removed _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recovered_state_mem k removed)]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_state_available_substitute σ τ k _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
