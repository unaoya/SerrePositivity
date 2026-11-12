module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitRefinement
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetAt
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInWedge

/-! # 元の左右部分集合の分割 augmentation
概要：元の左右部分集合の augmentation を共有頂点で貼り、全体への実射と照合する。
方針：元の分割射の左右制限と元の部分集合包含の可換三角形を使う。
規約：元の指定端点・全高次単体を保つ。使われ方：同じ cubical Hom 内の分割生成射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet
open SerrePositivity.InfinityCategories

/-- 元の左部分集合を、元の最小頂点から切断頂点への bead として読む。 -/
def necklaceInSimplexSubsetSplitLeft {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u})
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j) :=
  necklaceInSimplexSubsetAt (I.filter (· ≤ j)) _ j hL
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min (I.isLeast_min' _) (I.min'_le _ hj) _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _)

/-- 元の右部分集合を、元の切断頂点から最大頂点への bead として読む。 -/
def necklaceInSimplexSubsetSplitRight {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))) :=
  necklaceInSimplexSubsetAt (I.filter (j ≤ ·)) j _ hR
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max (I.isGreatest_max' _) (I.le_max' _ hj) _)

/-- 元の左右部分集合の augmentation を、元の同じ切断頂点で貼る。 -/
def necklaceInSimplexSubsetSplit {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u})
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (necklaceInSimplexSubsetSplitLeft I hI j hj hL)
    (necklaceInSimplexSubsetSplitRight I hI j hj hR)

/-- 元の分割射と全体の部分集合 augmentation の合成は、元の貼り合わせを回収する。 -/
lemma simplexSubsetSplitMap_augmentation {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    simplexSubsetSplitMap.{u} I j hj hL hR ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap I hI =
      (necklaceInSimplexSubsetSplit I hI j hj hL hR).map := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedge_hom_ext
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1))
  · rw [← Category.assoc, simplexSubsetSplitMap_inl I hI, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap_triangle]
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl (necklaceInSimplexSubsetSplitLeft I hI j hj hL)
      (necklaceInSimplexSubsetSplitRight I hI j hj hR)).symm
  · rw [← Category.assoc, simplexSubsetSplitMap_inr I hI, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap_triangle]
    exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr (necklaceInSimplexSubsetSplitLeft I hI j hj hL)
      (necklaceInSimplexSubsetSplitRight I hI j hj hR)).symm

/-- 元の貼り合わせと全体の部分集合 bead の間の、元の実可換三角形。 -/
def necklaceInSimplexSubsetSplitInclusion {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    necklaceInSimplexSubsetSplit.{u} I hI j hj hL hR ⟶ necklaceInSimplexSubset I hI where
  necklaceHom := simplexSubsetSplitRefinement I j hj hL hR
  w := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap I hI)
      (simplexSubsetSplitRefinement_triangle I j hj hL hR)).trans
      (simplexSubsetSplitMap_augmentation I hI j hj hL hR))

/-- 元の分割 augmentation の実可換三角形は、同じ cubical Hom の表示関係を与える。 -/
lemma necklaceInSimplexSubsetSplitInclusion_cell {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    necklaceCubicalSet.map (simplexSubsetSplitRefinement.{u} I j hj hL hR) ≫
        necklaceCubicalCell (necklaceInSimplexSubset I hI) =
      necklaceCubicalCell (necklaceInSimplexSubsetSplit I hI j hj hL hR) :=
  necklaceCubicalCell_relation (necklaceInSimplexSubsetSplitInclusion I hI j hj hL hR)

end SerrePositivity.KST.SConstruction
