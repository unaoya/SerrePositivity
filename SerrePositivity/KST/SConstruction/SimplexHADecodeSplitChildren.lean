module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCellRecursion
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaNecklaceComparison

/-! # 元の部分集合分割の左右 necklace と読み替え側の実鎖射
概要：元の左 necklace を前段の読み替え実生成射へ、右 necklace を右側 bead へ移す。
方針：元の左右フィルターの集合等号と、元の同端点実生成射の比較を合成する。
規約：元の鎖射全体と端点を保持。使われ方：読み替え次元の標準一面の合成式。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の左部分集合の necklace 生成射は、元の前段の読み替えの実生成射に戻る。 -/
lemma simplexHADecodeSplitLeft_cell_heq {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (necklaceLambdaCell A (necklaceInSimplexSubsetSplitLeft.{u}
      (simplexHADecodeSubset (m + 1) v T) (simplexHADecodeSubset_two (m + 1) v T hT hb)
      (v (Fin.last (m + 1))) (simplexHADecodeSubset_cut_mem m v T)
      (simplexHADecodeSubset_left_two m v T hb)))
      (simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v)
        {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v)) := by
  let I := simplexHADecodeSubset (m + 1) v T
  let r := v (Fin.last (m + 1))
  have hI : 2 ≤ I.card := simplexHADecodeSubset_two (m + 1) v T hT hb
  have hj : r ∈ I := simplexHADecodeSubset_cut_mem m v T
  have hL := simplexHADecodeSubset_left_two m v T hb
  have hc := necklaceLambdaCell_subsetAt_canonical_heq A (I.filter (· ≤ r))
    (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) r hL
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min (I.isLeast_min' _) (I.min'_le r hj) _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _)
  exact hc.trans ((simplexSubsetLambdaCell_heq_of_eq A _ _
    (simplexHADecodeSubset_filter_left_decode m v T hb) _ _).trans
      (simplexHADecodeSubsetCell_canonical_heq A m (Fin.castSuccOrderEmb.trans v)
        {r} (Finset.singleton_nonempty r) (simplexHADecodePrefix_cut m v)).symm)

/-- 元の右部分集合の necklace 生成射は、同じ元の右側集合と切断頂点の bead 鎖射。 -/
lemma simplexHADecodeSplitRight_cell_heq {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (necklaceLambdaCell A (necklaceInSimplexSubsetSplitRight.{u}
      (simplexHADecodeSubset (m + 1) v T) (simplexHADecodeSubset_two (m + 1) v T hT hb)
      (v (Fin.last (m + 1))) (simplexHADecodeSubset_cut_mem m v T)
      (simplexHADecodeSubset_right_two m v T hT hb)))
      (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb)) := by
  let I := simplexHADecodeSubset (m + 1) v T
  let r := v (Fin.last (m + 1))
  have hI : 2 ≤ I.card := simplexHADecodeSubset_two (m + 1) v T hT hb
  have hj : r ∈ I := simplexHADecodeSubset_cut_mem m v T
  have hR := simplexHADecodeSubset_right_two m v T hT hb
  have hc := necklaceLambdaCell_subsetAt_canonical_heq A (I.filter (r ≤ ·)) r
    (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max (I.isGreatest_max' _) (I.le_max' r hj) _)
  have he : I.filter (r ≤ ·) = insert r T := simplexHADecodeSubset_filter_right m v T hb
  change 2 ≤ (I.filter (r ≤ ·)).card at hR
  have hJ : 2 ≤ (insert r T).card := by simpa only [he] using hR
  have hmin : r = (insert r T).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hJ) := by
    simpa only [he] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hR)
  have hmax : T.max' hT = (insert r T).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hJ) :=
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT r hb).symm
  exact hc.trans ((simplexSubsetLambdaCell_heq_of_eq A _ _ he _ hJ).trans
    (simplexHABeadTail_cell_canonical_heq A T hT r hb hJ hmin hmax).symm)

end SerrePositivity.KST.SConstruction
