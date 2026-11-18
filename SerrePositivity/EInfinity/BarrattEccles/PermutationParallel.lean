module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationParallelValues

/-!
# 置換の部分合成の並列結合則

概要：Berger–Fresse §0.10 の異なる二入力への置換の代入が順序に依存しないことを示す。
方針：最終入力を元の外側の残りと二つの挿入区間へ分け、各値を数値の位置の公式で比較する。
規約：指定する二入力は異なるが、前後の順序は仮定しない。
使われ方：三入力の shuffle の並列結合則の頂点の比較に用いる。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：異なる二入力への置換の部分合成は挿入順序によらず一致する（Berger–Fresse §0.10）。
方針：二つの挿入区間と残りの入力で位置と置換の値を比較する。
規約：最終 arity の入れ替えを Fin の同値による共役で表す。
使われ方：部分合成の並列結合則の置換列の各頂点を同定する。 -/
lemma permutationComposition_parallel_assoc (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (σ : Equiv.Perm (Fin (m + 2))) (τ : Equiv.Perm (Fin n)) (υ : Equiv.Perm (Fin k)) :
    (finCongr (by omega : m + n + k = m + k + n)).permCongr
        (permutationComposition (m + n) k (parallelSlot m n i j hji)
          (permutationAfterInsertion m n i σ τ) υ) =
      permutationComposition (m + k) n (parallelSlot m k j i hji.symm)
        (permutationAfterInsertion m k j σ υ) τ := by
  let P := permutationAfterInsertion m n i σ τ
  let Q := permutationAfterInsertion m k j σ υ
  let sL := parallelSlot m n i j hji
  let sR := parallelSlot m k j i hji.symm
  let ht : m + n + k = m + k + n := by omega
  have hPslot : (P sL).val = remainingValue n (σ i).val (σ j).val :=
    permutationAfterInsertion_slot m n i j hji σ τ
  have hQslot : (Q sR).val = remainingValue k (σ j).val (σ i).val :=
    permutationAfterInsertion_slot m k j i hji.symm σ υ
  apply Equiv.ext
  intro x
  change Fin.cast ht (permutationComposition (m + n) k sL P υ (Fin.cast ht.symm x)) =
    permutationComposition (m + k) n sR Q τ x
  obtain ⟨b, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv (m + k) n sR).symm.surjective x
  cases b with
  | inl b =>
    change Fin.cast ht
      (permutationComposition (m + n) k sL P υ
        (Fin.cast ht.symm (remainingPosition (m + k) n sR b))) =
      permutationComposition (m + k) n sR Q τ (remainingPosition (m + k) n sR b)
    obtain ⟨a, ha⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv (m + 1) k j).symm.surjective
      (Fin.cast (by omega : m + k + 1 = m + 1 + k) b.val)
    cases a with
    | inl a =>
      have hb : b.val = Fin.cast (by omega : m + 1 + k = m + k + 1)
          (remainingPosition (m + 1) k j a) := by
        apply Fin.ext
        exact (congrArg Fin.val ha).symm
      have hai : a.val ≠ i := by
        intro hai
        apply b.property
        apply Fin.ext
        rw [hb]
        simp only [Fin.val_cast, remainingPosition_val, sR, parallelSlot_val, hai]
      let A : {a : Fin (m + 2) // a ≠ i ∧ a ≠ j} := ⟨a.val, hai, a.property⟩
      have hb' : b = parallelOuterRemaining m k j i hji.symm
          ⟨A.val, A.property.2, A.property.1⟩ := Subtype.ext hb
      have hc := parallelPosition_outer m n k i j hji A
      have hx : Fin.cast ht.symm (remainingPosition (m + k) n sR b) =
          remainingPosition (m + n) k sL (parallelOuterRemaining m n i j hji A) := by
        apply Fin.ext
        exact (congrArg Fin.val (congrArg (remainingPosition (m + k) n sR) hb')).trans
          (congrArg Fin.val hc).symm
      rw [hx]
      apply Fin.ext
      simp only [Fin.val_cast]
      rw [permutationComposition_remaining_val, permutationComposition_remaining_val,
        hPslot, hQslot]
      have hPa : (P (parallelOuterRemaining m n i j hji A).val).val =
          remainingValue n (σ i).val (σ a.val).val :=
        permutationAfterInsertion_remaining m n i σ τ ⟨a.val, hai⟩
      have hQa : (Q b.val).val = remainingValue k (σ j).val (σ a.val).val := by
        rw [hb]
        exact permutationAfterInsertion_remaining m k j σ υ a
      rw [hPa, hQa]
      exact remainingValue_parallel n k (σ i).val (σ j).val (σ a.val).val
        (fun h => hji (σ.injective (Fin.ext h)).symm)
        (fun h => hai (σ.injective (Fin.ext h)))
        (fun h => a.property (σ.injective (Fin.ext h)))
    | inr a =>
      have hb : b.val = Fin.cast (by omega : m + 1 + k = m + k + 1)
          (insertedPosition (m + 1) k j a) := by
        apply Fin.ext
        exact (congrArg Fin.val ha).symm
      have hb' : b = parallelInnerRemaining m k j i hji.symm a := Subtype.ext hb
      have hc := parallelPosition_inside m k n j i hji.symm a
      have hx : Fin.cast ht.symm (remainingPosition (m + k) n sR b) =
          insertedPosition (m + n) k sL a := by
        apply Fin.ext
        exact (congrArg Fin.val (congrArg (remainingPosition (m + k) n sR) hb')).trans
          (congrArg Fin.val hc)
      rw [hx, permutationComposition_inside]
      apply Fin.ext
      simp only [Fin.val_cast, insertedPosition_val]
      rw [permutationComposition_remaining_val, hPslot, hQslot]
      have hQa : (Q b.val).val = (σ j).val + (υ a).val := by
        rw [hb]
        exact permutationAfterInsertion_inside m k j σ υ a
      rw [hQa]
      exact (insertedValue_parallel k n (σ j).val (σ i).val (υ a).val
        (fun h => hji (σ.injective (Fin.ext h))) (υ a).isLt).symm
  | inr a =>
    change Fin.cast ht
      (permutationComposition (m + n) k sL P υ
        (Fin.cast ht.symm (insertedPosition (m + k) n sR a))) =
      permutationComposition (m + k) n sR Q τ (insertedPosition (m + k) n sR a)
    have hc := parallelPosition_inside m n k i j hji a
    have hx : Fin.cast ht.symm (insertedPosition (m + k) n sR a) =
        remainingPosition (m + n) k sL (parallelInnerRemaining m n i j hji a) := by
      apply Fin.ext
      exact (congrArg Fin.val hc).symm
    rw [hx, permutationComposition_inside]
    apply Fin.ext
    simp only [Fin.val_cast, insertedPosition_val]
    rw [permutationComposition_remaining_val, hPslot, hQslot]
    have hPa : (P (parallelInnerRemaining m n i j hji a).val).val =
        (σ i).val + (τ a).val := permutationAfterInsertion_inside m n i σ τ a
    rw [hPa]
    exact insertedValue_parallel n k (σ i).val (σ j).val (τ a).val
      (fun h => hji (σ.injective (Fin.ext h)).symm) (τ a).isLt

/-- 概要：前後に並ぶ二入力への置換の代入は標準の位置の表記で並列結合則を満たす（Berger–Fresse §0.10）。
方針：順序を仮定しない並列結合則の二回目の位置を前後の不等式で簡約する。
規約：最初の位置 i は j より前であり、後方の位置は j+n−1 へ移る。
使われ方：対称オペラッドの parallel_assoc の添字へ合わせる。 -/
lemma permutationComposition_parallel_assoc_ordered (m n k : ℕ) (i j : Fin (m + 2))
    (hij : i.val < j.val) (σ : Equiv.Perm (Fin (m + 2)))
    (τ : Equiv.Perm (Fin n)) (υ : Equiv.Perm (Fin k)) :
    (finCongr (by omega : m + n + k = m + k + n)).permCongr
        (permutationComposition (m + n) k ⟨j.val + n - 1, by omega⟩
          (permutationAfterInsertion m n i σ τ) υ) =
      permutationComposition (m + k) n ⟨i.val, by omega⟩
        (permutationAfterInsertion m k j σ υ) τ := by
  have hji : j ≠ i := fun h => by have hv := congrArg Fin.val h; omega
  have hL : parallelSlot m n i j hji = ⟨j.val + n - 1, by omega⟩ := by
    apply Fin.ext
    rw [parallelSlot_val]
    exact ite_eq_right (by omega)
  have hR : parallelSlot m k j i hji.symm = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rw [parallelSlot_val]
    exact ite_eq_left hij
  simpa only [hL, hR] using permutationComposition_parallel_assoc m n k i j hji σ τ υ

end SerrePositivity.EInfinity.BarrattEccles
