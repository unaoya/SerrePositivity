module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitAugmentation
public import SerrePositivity.KST.SConstruction.NecklaceCubicalComposition

/-! # 元の部分集合分割と実 cubical tensor 合成
概要：元の左右部分集合の cubical 合成を、元の全体 bead の生成射に戻す。
方針：元の合成の両生成射への制限と、元の分割可換三角形を合成する。
規約：元の Day tensor と連結比較を保持。使われ方：Serre tensor の最高生成元への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の左右部分集合の実 cubical 合成は、元の tensor 比較と分割 refinement を回収する。 -/
lemma simplexSubsetSplitCubicalTensor_composition {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    cubicalDayTensorMap
        (necklaceCubicalCell (necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL))
        (necklaceCubicalCell (necklaceInSimplexSubsetSplitRight I hI j hj hR)) ≫
      necklaceCubicalCompose Δ[n]
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))) =
      (necklaceCubicalTensorIso (necklaceBead ((I.filter (· ≤ j)).card - 1))
        (necklaceBead ((I.filter (j ≤ ·)).card - 1))).hom ≫
      necklaceCubicalSet.map (simplexSubsetSplitRefinement I j hj hL hR) ≫
        necklaceCubicalCell (necklaceInSimplexSubset I hI) := by
  exact (necklaceCubicalCompose_cell _ _ _ _
    (necklaceInSimplexSubsetSplitLeft I hI j hj hL)
    (necklaceInSimplexSubsetSplitRight I hI j hj hR)).trans
      (congrArg (fun f => (necklaceCubicalTensorIso
        (necklaceBead ((I.filter (· ≤ j)).card - 1))
        (necklaceBead ((I.filter (j ≤ ·)).card - 1))).hom ≫ f)
        (necklaceInSimplexSubsetSplitInclusion_cell I hI j hj hL hR).symm)

end SerrePositivity.KST.SConstruction
