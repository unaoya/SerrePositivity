module
public import SerrePositivity.KST.SConstruction.NecklaceLambdaTopComposition
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitLambdaCell

/-! # 元の左右部分集合の分割生成射の最高生成元像
概要：元の全体 bead の Serre 生成射を分割して評価すると、元の左右成分の合成を回収する。
方針：元の実 refinement の表示関係と、全 necklace の最高生成元合成則を使う。
規約：元の Hom と実鎖射を保持。使われ方：HA の同じ有限部分集合の合成項。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の分割 refinement の実最高生成元像は、元の左右 necklace 成分の通常順合成。 -/
lemma simplexSubsetSplit_top_composition {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    let T := necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL
    let U := necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR
    serreCubeTopCellImage A (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
      (T.necklace.down.dimension + U.necklace.down.dimension)
      ((serreConcreteCubeComplexFunctor A).map
          (necklaceCubeTensorIso T.necklace U.necklace).hom ≫
        (serreConcreteCubeComplexFunctor A).map
          (necklaceConcreteCubeMap (simplexSubsetSplitRefinement I j hj hL hR)) ≫
            necklaceLambdaCell A (necklaceInSimplexSubset I hI)) =
      compose A
        (serreCubeTopCellImage A (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j)
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
          U.necklace.down.dimension (necklaceLambdaCell A U))
        (serreCubeTopCellImage A (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j)) T.necklace.down.dimension (necklaceLambdaCell A T))
        (by omega) := by
  exact (congrArg
    (fun f => serreCubeTopCellImage A _
      ((necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace.down.dimension +
        (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace.down.dimension)
      ((serreConcreteCubeComplexFunctor A).map (necklaceCubeTensorIso
        (necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace
        (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace).hom ≫ f))
    (simplexSubsetSplitLambdaCell_relation A I hI j hj hL hR)).trans
      (necklaceLambdaCell_top_composition A
        (necklaceInSimplexSubsetSplitLeft I hI j hj hL)
        (necklaceInSimplexSubsetSplitRight I hI j hj hR))

end SerrePositivity.KST.SConstruction
