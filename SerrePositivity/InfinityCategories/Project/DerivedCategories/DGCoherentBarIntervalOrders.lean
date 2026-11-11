module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarCuts
/-!
概要：coherent bar の切断に使う区間順序写像と、面との合成を比較する。
方針：区間の始点と長さを分け、同じ Fin 型の写像として成分を計算する。
規約：元の単体写像の厳密な等号を示し、添字の宇宙や図式を変更しない。
使われ方：bar の面・prefix・tail の二段合成の照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

def dgCoherentBarIntervalOrder (n a l : ℕ) (h : a + l ≤ n) :
    Fin (l + 1) →o Fin (n + 1) where
  toFun j := ⟨a + j.val, by omega⟩
  monotone' := fun _ _ hj => Nat.add_le_add_left hj a

lemma dgCoherentBarIntervalOrder_comp (n a l b m : ℕ)
    (h : a + l ≤ n) (h' : b + m ≤ l) :
    (dgCoherentBarIntervalOrder n a l h).comp (dgCoherentBarIntervalOrder l b m h') =
      dgCoherentBarIntervalOrder n (a + b) m (by omega) := by
  ext j
  exact (Nat.add_assoc a b j.val).symm

lemma dgCoherentBarPrefixOrder_interval (n k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder n k h = dgCoherentBarIntervalOrder n 0 k (by omega) := by
  ext j
  exact (Nat.zero_add j.val).symm

lemma dgCoherentBarTailOrder_interval (n k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder n k h = dgCoherentBarIntervalOrder n k (n - k) (by omega) := rfl

lemma dgCoherentBarIntervalOrder_face (n a l : ℕ) (h : a + l ≤ n) (i : Fin (l + 2)) :
    SimplexCategory.mkHom (dgCoherentBarIntervalOrder n a l h) ≫
        SimplexCategory.δ (⟨a + i.val, by omega⟩ : Fin (n + 2)) =
      SimplexCategory.δ i ≫
        SimplexCategory.mkHom (dgCoherentBarIntervalOrder (n + 1) a (l + 1) (by omega)) := by
  apply SimplexCategory.Hom.ext
  ext j
  have hj : j.val < l + 1 := j.isLt
  change ((⟨a + i.val, by omega⟩ : Fin (n + 2)).succAbove
    ⟨a + j.val, by omega⟩).val = a + (i.succAbove j).val
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
    Fin.val_mk, Nat.add_lt_add_iff_left]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk] <;> omega

lemma dgCoherentBarIntervalOrder_face_after (n a l : ℕ) (h : a + l ≤ n)
    (i : Fin (n + 2)) (hi : a + l < i.val) :
    SimplexCategory.mkHom (dgCoherentBarIntervalOrder n a l h) ≫ SimplexCategory.δ i =
      SimplexCategory.mkHom (dgCoherentBarIntervalOrder (n + 1) a l (by omega)) := by
  apply SimplexCategory.Hom.ext
  ext j
  have hj : j.val < l + 1 := j.isLt
  change (i.succAbove ⟨a + j.val, by omega⟩).val = a + j.val
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change a + j.val < i.val
    omega

lemma dgCoherentBarIntervalOrder_face_before (n a l : ℕ) (h : a + l ≤ n)
    (i : Fin (n + 2)) (hi : i.val ≤ a) :
    SimplexCategory.mkHom (dgCoherentBarIntervalOrder n a l h) ≫ SimplexCategory.δ i =
      SimplexCategory.mkHom (dgCoherentBarIntervalOrder (n + 1) (a + 1) l (by omega)) := by
  apply SimplexCategory.Hom.ext
  ext j
  have hj : j.val < l + 1 := j.isLt
  change (i.succAbove ⟨a + j.val, by omega⟩).val = a + 1 + j.val
  rw [Fin.succAbove_of_le_castSucc]
  · simp only [Fin.val_succ, Fin.val_mk]
    omega
  · change i.val ≤ a + j.val
    omega

end SerrePositivity.InfinityCategories.Project.DerivedCategories
