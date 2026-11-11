module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCell
public import SerrePositivity.KST.SConstruction.SimplexHABeadTailComparison

/-! # 元の読み替え次元の実生成射の基底と辺保持
概要：左列が一点の基底と、最右頂点を右側集合へ移す辺保持を元の実鎖射で回収する。
方針：元の部分集合の等号と、元の指定端点・次元からの回収の異種等号を合成する。
規約：元の部分集合と実鎖射を保持。使われ方：全生成元語の標準面との帰納的同定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の最右頂点を右側集合へ移しても、同じ元の部分集合の実生成射を回収する。 -/
lemma simplexHADecodeSubsetCell_edge {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v)
      (insert (v (Fin.last (m + 1))) T) (Finset.insert_nonempty _ T)
      (simplexHADecodePrefix_insert m v T hb))
      (simplexHADecodeSubsetCell A (m + 1) v T hT hb) :=
  simplexHADecodeSubsetCell_congr_heq A m (m + 1) _ _ _ _ _ _ _ _
    (simplexHADecodeSubset_insert_tail m v T)

/-- 元の左列が一点の実生成射は、同じ右側集合と左端点から作った元の語の実鎖射。 -/
lemma simplexHADecodeSubsetCell_zero {n : ℕ} (v : Fin 1 ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) (hb : ∀ t ∈ T, v (Fin.last 0) < t) :
    HEq (simplexHADecodeSubsetCell A 0 v T hT hb)
      (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v 0) hb)) := by
  have hI : 2 ≤ (insert (v 0) T).card := by
    simpa only [simplexHADecodeSubset_zero] using simplexHADecodeSubset_two 0 v T hT hb
  have hmin : v 0 = (insert (v 0) T).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI) := by
    simpa only [simplexHADecodeSubset_zero] using (simplexHADecodeSubset_min 0 v T hb).symm
  have hmax : T.max' hT = (insert (v 0) T).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI) := by
    simpa only [simplexHADecodeSubset_zero] using (simplexHADecodeSubset_max 0 v T hT hb).symm
  exact (simplexHADecodeSubsetCell_canonical_heq A 0 v T hT hb).trans
    ((simplexSubsetLambdaCell_heq_of_eq A _ _ (simplexHADecodeSubset_zero v T) _ hI).trans
      (simplexHABeadTail_cell_canonical_heq A T hT (v 0) hb hI hmin hmax).symm)

end SerrePositivity.KST.SConstruction
