module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingSimplex

/-!
概要：元の奇数頂点を除いた面の、隣接する二つの Y を潰す順序射。
方針：元の頂点番号で場合分けし、偶奇と潰れる二位置を厳密に計算する。
規約：元の余面の包含を使い、短い交互列の頂点番号を保持する。
使われ方：Ret の隣接段階の元の逆像境界の照合。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の奇数頂点は、元の交互列の両端の内部にある。 -/
lemma oddVertex_bounds {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1) :
    0 < j.val ∧ j.val ≤ 2 * m + 1 := by
  have h := j.isLt
  omega

/-- 元の奇数頂点を除いた面の、隣り合う二つの Y を潰す元の順序射。 -/
def oddFaceCollapse {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1) :
    Fin (2 * m + 2) →o Fin (2 * m + 1) where
  toFun a := ⟨if a.val < j.val then a.val else a.val - 1, by
    have h := (oddVertex_bounds j hj).2
    have ha := a.isLt
    split_ifs <;> omega⟩
  monotone' a b hab := by
    change (if a.val < j.val then a.val else a.val - 1) ≤
      if b.val < j.val then b.val else b.val - 1
    have hab' : a.val ≤ b.val := hab
    split_ifs <;> omega

/-- 元の奇数頂点の包含の頂点番号。 -/
lemma oddFaceInsert_val {m : ℕ} (j : Fin (2 * m + 3)) (a : Fin (2 * m + 2)) :
    (j.succAbove a).val = if a.val < j.val then a.val else a.val + 1 := by
  by_cases h : a.val < j.val
  · rw [ite_eq_left h, Fin.succAbove_of_castSucc_lt j a (show a.castSucc < j from h)]
    rfl
  · rw [ite_eq_right h, Fin.succAbove_of_le_castSucc j a
      (show j ≤ a.castSucc from Nat.le_of_not_gt h)]
    rfl

/-- 元の奇数頂点の面と潰した短い列は、元の頂点の偶奇を保持する。 -/
lemma oddFaceCollapse_parity {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1)
    (a : Fin (2 * m + 2)) :
    (j.succAbove a).val % 2 = (oddFaceCollapse j hj a).val % 2 := by
  rw [oddFaceInsert_val]
  change (if a.val < j.val then a.val else a.val + 1) % 2 =
    (if a.val < j.val then a.val else a.val - 1) % 2
  have hp := (oddVertex_bounds j hj).1
  split_ifs <;> omega

/-- 異なる二位置が潰れる場合、その二位置は元の隣り合う二つの Y の位置。 -/
lemma oddFaceCollapse_fiber {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1)
    {a b : Fin (2 * m + 2)} (hab : a < b) (he : oddFaceCollapse j hj a = oddFaceCollapse j hj b) :
    a.val = j.val - 1 ∧ b.val = j.val := by
  have hv := congrArg Fin.val he
  change (if a.val < j.val then a.val else a.val - 1) =
    (if b.val < j.val then b.val else b.val - 1) at hv
  have hp := (oddVertex_bounds j hj).1
  have hab' : a.val < b.val := hab
  split_ifs at hv <;> omega

/-- 潰れる二位置の像は、短い交互列の元の分裂対象 Y。 -/
lemma oddFaceCollapse_fiber_image {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1)
    {a b : Fin (2 * m + 2)} (hab : a < b) (he : oddFaceCollapse j hj a = oddFaceCollapse j hj b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject.{u} (oddFaceCollapse j hj a).val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage := by
  have ha := (oddFaceCollapse_fiber j hj hab he).1
  have hp := (oddVertex_bounds j hj).1
  have hv : (oddFaceCollapse j hj a).val % 2 ≠ 1 := by
    change (if a.val < j.val then a.val else a.val - 1) % 2 ≠ 1
    split_ifs <;> omega
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject, ite_eq_right hv]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
