module
public import SerrePositivity.KST.SConstruction.NecklaceLambdaMappedTop
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitLambdaCell

/-! # 元の実 dg 関手における部分集合分割の最高生成元像
概要：元の部分集合の実分割射の最高生成元像は、同じ dg 関手の左右成分の通常順合成。
方針：元の実三角形の Serre 関係と、元の dg 関手付き連結生成元評価を使う。
規約：元の有限部分集合・指定端点・実 Hom 射を保持。使われ方：native HA の合成項。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の部分集合分割を実 dg 関手で送った最高生成元像は、元の左右成分の通常順合成。 -/
lemma simplexSubsetSplit_top_composition_post {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    let a := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    let b := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j
    let c := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    let T := necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL
    let U := necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR
    serreCubeTopCellImage A (homObject A D (F.obj a) (F.obj c))
        (T.necklace.down.dimension + U.necklace.down.dimension)
        (((serreConcreteCubeComplexFunctor A).map
            (necklaceCubeTensorIso T.necklace U.necklace).hom ≫
          (serreConcreteCubeComplexFunctor A).map
            (necklaceConcreteCubeMap (simplexSubsetSplitRefinement I j hj hL hR)) ≫
              necklaceLambdaCell A (necklaceInSimplexSubset I hI)) ≫ F.map a c) =
      compose A
        (serreCubeTopCellImage A (homObject A D (F.obj b) (F.obj c)) U.necklace.down.dimension
          (necklaceLambdaCell A U ≫ F.map b c))
        (serreCubeTopCellImage A (homObject A D (F.obj a) (F.obj b)) T.necklace.down.dimension
          (necklaceLambdaCell A T ≫ F.map a b)) (by omega) := by
  exact (congrArg
    (fun f => serreCubeTopCellImage A _
      ((necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace.down.dimension +
        (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace.down.dimension)
      (((serreConcreteCubeComplexFunctor A).map (necklaceCubeTensorIso
        (necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace
        (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace).hom ≫ f) ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))))
    (simplexSubsetSplitLambdaCell_relation A I hI j hj hL hR)).trans
      (necklaceLambdaCell_top_composition_post A F
        (necklaceInSimplexSubsetSplitLeft I hI j hj hL)
        (necklaceInSimplexSubsetSplitRight I hI j hj hR))

end SerrePositivity.KST.SConstruction
