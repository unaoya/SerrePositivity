module

public import SerrePositivity.EInfinity.BarrattEccles.NestedPositions

/-!
# 置換の部分合成の入れ子結合則

概要：Berger–Fresse §0.10 の置換の部分合成の入れ子の結合則を証明する。
方針：最終入力を外側の残り・中間の残り・最内層の三種類に分けて値を比較する。
規約：最終 arity の括弧を Fin 上の置換の共役で移送する。
使われ方：shuffle 部分合成の入れ子結合則を頂点ごとに比較する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：置換の部分合成は同じ入力への入れ子の代入に関して結合的である（Berger–Fresse §0.10）。
方針：挿入分解を二回適用して三種類の入力へ分け、二段の位置計算の公式を使う。
規約：内側の二回目の位置は i+j、最内層の arity k は0でもよい。
使われ方：三入力の shuffle の各頂点の置換を同定する。 -/
lemma permutationComposition_nested_assoc (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin (n + 1))) (υ : Equiv.Perm (Fin k)) :
    (finCongr (Nat.add_assoc m n k)).permCongr
        (permutationComposition (m + n) k (nestedSlot m n i j)
          (permutationComposition m (n + 1) i σ τ) υ) =
      permutationComposition m (n + k) i σ (permutationComposition n k j τ υ) := by
  let P : Equiv.Perm (Fin (m + n + 1)) := permutationComposition m (n + 1) i σ τ
  let Q := permutationComposition n k j τ υ
  have hPslot : (P (nestedSlot m n i j)).val = (σ i).val + (τ j).val :=
    congrArg Fin.val (permutationComposition_inside m (n + 1) i σ τ j)
  apply Equiv.ext
  intro x
  change Fin.cast (Nat.add_assoc m n k)
    (permutationComposition (m + n) k (nestedSlot m n i j) P υ
      (Fin.cast (Nat.add_assoc m n k).symm x)) = permutationComposition m (n + k) i σ Q x
  obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m (n + k) i).symm.surjective x
  cases a with
  | inl a =>
    change Fin.cast (Nat.add_assoc m n k)
      (permutationComposition (m + n) k (nestedSlot m n i j) P υ
        (Fin.cast (Nat.add_assoc m n k).symm (remainingPosition m (n + k) i a))) =
      permutationComposition m (n + k) i σ Q (remainingPosition m (n + k) i a)
    have hx : Fin.cast (Nat.add_assoc m n k).symm (remainingPosition m (n + k) i a) =
        remainingPosition (m + n) k (nestedSlot m n i j) (nestedOuterRemaining m n i j a) := by
      apply Fin.ext
      exact (congrArg Fin.val (nestedPosition_outer m n k i j a)).symm
    rw [hx]
    apply Fin.ext
    simp only [Fin.val_cast]
    rw [permutationComposition_remaining_val, permutationComposition_remaining_val]
    change remainingValue k (P (nestedSlot m n i j)).val
      (P (remainingPosition m (n + 1) i a)).val = _
    rw [hPslot]
    have hPrem : (P (remainingPosition m (n + 1) i a)).val =
        remainingValue (n + 1) (σ i).val (σ a.val).val :=
      permutationComposition_remaining_val m (n + 1) i σ τ a
    rw [hPrem]
    exact remainingValue_nested_outer n k (σ i).val (τ j).val (σ a.val).val
      (Nat.le_of_lt_succ (τ j).isLt) (fun h => a.property (σ.injective (Fin.ext h)))
  | inr b =>
    obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv n k j).symm.surjective b
    cases a with
    | inl a =>
      change Fin.cast (Nat.add_assoc m n k)
        (permutationComposition (m + n) k (nestedSlot m n i j) P υ
          (Fin.cast (Nat.add_assoc m n k).symm
            (insertedPosition m (n + k) i (remainingPosition n k j a)))) =
        permutationComposition m (n + k) i σ Q
          (insertedPosition m (n + k) i (remainingPosition n k j a))
      have hx : Fin.cast (Nat.add_assoc m n k).symm
          (insertedPosition m (n + k) i (remainingPosition n k j a)) =
          remainingPosition (m + n) k (nestedSlot m n i j) (nestedInnerRemaining m n i j a) := by
        apply Fin.ext
        exact (congrArg Fin.val (nestedPosition_inner m n k i j a)).symm
      rw [hx, permutationComposition_inside]
      apply Fin.ext
      simp only [Fin.val_cast, insertedPosition_val]
      rw [permutationComposition_remaining_val]
      change remainingValue k (P (nestedSlot m n i j)).val
        (P (insertedPosition m (n + 1) i a.val)).val =
          (σ i).val + (Q (remainingPosition n k j a)).val
      rw [hPslot]
      have hPin : (P (insertedPosition m (n + 1) i a.val)).val =
          (σ i).val + (τ a.val).val :=
        congrArg Fin.val (permutationComposition_inside m (n + 1) i σ τ a.val)
      have hQrem : (Q (remainingPosition n k j a)).val =
          remainingValue k (τ j).val (τ a.val).val :=
        permutationComposition_remaining_val n k j τ υ a
      rw [hPin, hQrem]
      exact remainingValue_nested_inner k (σ i).val (τ j).val (τ a.val).val
        (fun h => a.property (τ.injective (Fin.ext h)))
    | inr a =>
      change Fin.cast (Nat.add_assoc m n k)
        (permutationComposition (m + n) k (nestedSlot m n i j) P υ
          (Fin.cast (Nat.add_assoc m n k).symm
            (insertedPosition m (n + k) i (insertedPosition n k j a)))) =
        permutationComposition m (n + k) i σ Q
          (insertedPosition m (n + k) i (insertedPosition n k j a))
      have hx : Fin.cast (Nat.add_assoc m n k).symm
          (insertedPosition m (n + k) i (insertedPosition n k j a)) =
          insertedPosition (m + n) k (nestedSlot m n i j) a := by
        apply Fin.ext
        exact (congrArg Fin.val (nestedPosition_inside m n k i j a)).symm
      rw [hx, permutationComposition_inside, permutationComposition_inside]
      apply Fin.ext
      simp only [Fin.val_cast, insertedPosition_val]
      rw [hPslot]
      have hQin : (Q (insertedPosition n k j a)).val = (τ j).val + (υ a).val :=
        congrArg Fin.val (permutationComposition_inside n k j τ υ a)
      rw [hQin]
      exact Nat.add_assoc _ _ _

end SerrePositivity.EInfinity.BarrattEccles
