module
public import SerrePositivity.KST.SConstruction.SimplexSubsetInclusionRange
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index
public import Mathlib.Order.Interval.Finset.Fin

/-! # 元の左右フィルターの局所頂点像
概要：元の内部頂点で切った左右部分集合の包含の像は、元の局所番号の始端・終端区間。
方針：元の所属条件を、同じ昇順列挙の厳密な順序と逆の回収式で判定する。
規約：元の切断頂点を両ブロックに含める。使われ方：左右ブロックの濃度と番号の同定。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.InfinityCategories

/-- 元の左フィルターには、元の最小頂点と切断頂点の二点が残る。 -/
lemma simplexSubsetSplitLeft_two {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j) :
    2 ≤ (I.filter (· ≤ j)).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two (I.min'_mem _) hj hjm

/-- 元の右フィルターには、元の切断頂点と最大頂点の二点が残る。 -/
lemma simplexSubsetSplitRight_two {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    2 ≤ (I.filter (j ≤ ·)).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj (I.max'_mem _) hjM

/-- 元の左フィルターの局所頂点像は、元の切断局所番号以下の始端区間。 -/
lemma simplexSubsetSplitLeft_range {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card) :
    Set.range (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (· ≤ j)) I hL hI (Finset.filter_subset _ _)) =
      Set.Iic (simplexSubsetVertexIndex I hI j hj) := by
  rw [simplexSubsetInclusionOrder_range]
  ext v
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v ∈ I.filter (· ≤ j) ↔ v ≤ simplexSubsetVertexIndex I hI j hj
  rw [Finset.mem_filter]
  have hm := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI v
  simp only [hm, true_and]
  exact (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v ≤ k)
    (simplexSubsetVertexIndex_recovery I hI j hj)).symm.trans
      (propext (simplexSubsetOrder_strictMono I hI).le_iff_le) |>.to_iff

/-- 元の右フィルターの局所頂点像は、元の切断局所番号以上の終端区間。 -/
lemma simplexSubsetSplitRight_range {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    Set.range (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (j ≤ ·)) I hR hI (Finset.filter_subset _ _)) =
      Set.Ici (simplexSubsetVertexIndex I hI j hj) := by
  rw [simplexSubsetInclusionOrder_range]
  ext v
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v ∈ I.filter (j ≤ ·) ↔ simplexSubsetVertexIndex I hI j hj ≤ v
  rw [Finset.mem_filter]
  have hm := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI v
  simp only [hm, true_and]
  exact (congrArg (fun k => k ≤ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v)
    (simplexSubsetVertexIndex_recovery I hI j hj)).symm.trans
      (propext (simplexSubsetOrder_strictMono I hI).le_iff_le) |>.to_iff

end SerrePositivity.KST.SConstruction
