module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecoveryLabels
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationCompositeRow
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapAvailable

/-!
模型。文献の定義との比較は後で
# 実際の合成置換行と任意の除外状態の内側射影

概要：Berger–Fresse §1.5.8 の逆構成で合成行を元の内側逆置換行へ戻す。
方針：既存の内側ラベル射影の部分単射性を示し、三ブロック表示を射影する。
規約：元の合成除外状態を仮定せず、任意の除外リストをそのまま射影する。
使われ方：合成表の実際の成功から内側表の成功を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：内側射影が b を返す文字は実際の挿入ラベル b（BF §1.5.8）。
方針：挿入ラベルの直和分解の同値で左右の成分を判別する。
規約：外側ラベルは none となる。
使われ方：内側射影を値を持つ部分で単射と扱う。 -/
lemma innerLabel_eq_some_iff {m n : ℕ} (k : Fin (m + 1))
    (a : Fin (m + n)) (b : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some b ↔ a = insertedPosition m n k b := by
  constructor
  · intro h
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).injective
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k a =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm (Sum.inr b))
    rw [Equiv.apply_symm_apply]
    cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k a with
    | inl c => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel, he, reduceCtorEq] at h
    | inr c =>
      have hc : c = b := by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel, he, Option.some.injEq] using h
      rw [hc]
  · intro h
    rw [h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_inserted]

/-- 概要：内側射影は値を持つ部分で単射（BF §1.5.8）。
方針：共通の射影値の実際の挿入ラベルとして両文字を同定する。
規約：外側ラベル同士の区別は要求しない。
使われ方：任意の除外状態での可用行射影を適用する。 -/
lemma innerLabel_partial_injective {m n : ℕ} (k : Fin (m + 1)) :
    ∀ a a' b, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel (n := n) k a = some b →
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a' = some b → a = a' := by
  intro a a' b ha ha'
  exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k a b).mp ha).trans
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k a' b).mp ha').symm

/-- 概要：外側文字の行は内側射影で空になる（BF §1.5.8）。
方針：残る外側ラベルの射影が全て none であることを使う。
規約：前半・後半の両方に適用できる。
使われ方：逆合成置換行の中央以外の部分を除く。 -/
lemma innerLabel_filterMap_remaining {m n : ℕ} (k : Fin (m + 1))
    (xs : List {a : Fin (m + 1) // a ≠ k}) :
    (xs.map (remainingPosition m n k)).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_remaining k b

/-- 概要：逆合成置換行の内側射影は元の内側逆置換行（BF §1.5.8）。
方針：三ブロック表示の外側を消し、中央の挿入写像を射影で戻す。
規約：外側置換と代入位置は任意、零 arity も含む。
使われ方：射影した抽出の行を実際の元の table の行へ同定する。 -/
lemma innerLabel_permutationComposition_row {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) :
    (List.ofFn (permutationComposition m n k σ τ).symm).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) =
      List.ofFn τ.symm := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow, List.filterMap_append,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_filterMap_remaining, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_filterMap_inserted, List.nil_append,
    List.append_nil]

/-- 概要：任意の除外状態の可用合成行も元の可用内側行へ戻る（BF §1.5.8）。
方針：内側射影の部分単射性による filterMap と除外の可換性を使う。
規約：除外状態が前向きに構成した形であることを要求しない。
使われ方：任意の成功合成 table の逆構成に適用する。 -/
lemma innerLabel_available_composition_row {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)).filterMap
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_permutationComposition_row]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
