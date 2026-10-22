module
public import SerrePositivity.KST.Fibration.WeakStringSimplicialIndices

/-! # 面・退化の合成箇所以外での元の連続辺の保存 -/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.KST.Fibration

/-- 面で除く頂点より前の連続辺は、そのまま元の連続辺である。 -/
lemma consecutiveWeakStringEdge_face_before (n : ℕ) (i : Fin (n + 2)) (j : Fin n)
    (h : j.val + 1 < i.val) :
    consecutiveWeakStringEdge n j ≫ SimplexCategory.δ i =
      consecutiveWeakStringEdge (n + 1) j.castSucc := by
  ext k
  have hk : k.val < 2 := k.isLt
  change (i.succAbove ⟨j.val + k.val, by omega⟩).val = j.val + k.val
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change j.val + k.val < i.val
    omega

/-- 面で除く頂点より後の連続辺は、元の次の連続辺である。 -/
lemma consecutiveWeakStringEdge_face_after (n : ℕ) (i : Fin (n + 2)) (j : Fin n)
    (h : i.val ≤ j.val) :
    consecutiveWeakStringEdge n j ≫ SimplexCategory.δ i =
      consecutiveWeakStringEdge (n + 1) j.succ := by
  ext k
  have hk : k.val < 2 := k.isLt
  change (i.succAbove ⟨j.val + k.val, by omega⟩).val = j.val + 1 + k.val
  rw [Fin.succAbove_of_le_castSucc]
  · simp
    omega
  · change i.val ≤ j.val + k.val
    omega

/-- 退化で繰り返す頂点より前の連続辺は、元の同じ連続辺である。 -/
lemma consecutiveWeakStringEdge_degeneracy_before (n : ℕ) (i : Fin (n + 1))
    (j : Fin n) (h : j.val < i.val) :
    consecutiveWeakStringEdge (n + 1) j.castSucc ≫ SimplexCategory.σ i =
      consecutiveWeakStringEdge n j := by
  ext k
  have hk : k.val < 2 := k.isLt
  change (i.predAbove ⟨j.val + k.val, by omega⟩).val = j.val + k.val
  rw [Fin.predAbove_of_le_castSucc]
  · rfl
  · change j.val + k.val ≤ i.val
    omega

/-- 退化で繰り返す頂点より後の連続辺も、添字を戻すと元の同じ連続辺である。 -/
lemma consecutiveWeakStringEdge_degeneracy_after (n : ℕ) (i : Fin (n + 1))
    (j : Fin n) (h : i.val ≤ j.val) :
    consecutiveWeakStringEdge (n + 1) j.succ ≫ SimplexCategory.σ i =
      consecutiveWeakStringEdge n j := by
  ext k
  have hk : k.val < 2 := k.isLt
  change (i.predAbove ⟨j.val + 1 + k.val, by omega⟩).val = j.val + k.val
  rw [Fin.predAbove_of_castSucc_lt]
  · simp
  · change i.val < j.val + 1 + k.val
    omega

end SerrePositivity.KST.Fibration
