module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitDegrees
public import SerrePositivity.KST.SConstruction.SimplexSubsetEraseNormalizedFace

/-! # 元の実分割 cube の濃度次元
概要：元の二 bead の連結 cube と全体 cube の次元を、元の削除・全体部分集合で読む。
方針：元の連結長の等号と元の余次元一を使う。
規約：元の実二 bead と同じ cube を保持。使われ方：標準一面の濃度次元への共役。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction

/-- 元の左右 bead の合計長の全体 cube の次元は、元の全体部分集合の濃度から二を除く。 -/
lemma simplexSubsetSplit_whole_dimension {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single
      (((I.filter (· ≤ j)).card - 1) + ((I.filter (j ≤ ·)).card - 1))).dimension = I.card - 2 :=
  (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single k).dimension)
    (simplexSubsetSplit_length I j hj hL hR)).trans
      (necklaceInSimplexSubset_dimension.{0} I hI)

/-- 元の正長二 bead の連結 cube は、元の内部点を削除した部分集合の濃度次元を持つ。 -/
lemma simplexSubsetSplit_wedge_erase_dimension {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedge
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1))).dimension = (I.erase j).card - 2 := by
  have hL := simplexSubsetSplitLeft_two I hI j hj hjm
  have hR := simplexSubsetSplitRight_two I hI j hj hjM
  have hc := necklaceWedgeBead_codimension
    ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1) (by omega) (by omega)
  have ht := simplexSubsetSplit_whole_dimension I hI j hj hL hR
  have he := simplexSubsetErase_normalized_codimension I hI j hj hjm hjM
  omega

end SerrePositivity.KST.SConstruction
