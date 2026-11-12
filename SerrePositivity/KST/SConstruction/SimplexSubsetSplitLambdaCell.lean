module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitOneFace
public import SerrePositivity.KST.SConstruction.NecklaceLambdaCell
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCell

/-! # 元の分割標準一面の Serre 生成射
概要：元の左右部分集合を貼った生成射を、元の標準一面から同じ Λ Hom 内で回収する。
方針：元の可換三角形を Serre 鎖へ送り、元の一面因子分解と合成する。
規約：元の鎖射と同じ端点を保持。使われ方：分割合成項の最高生成元への評価。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の部分集合の数値次元表示は、元の necklace Serre 生成射の次元移送。 -/
lemma simplexSubsetLambdaCell_necklace {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) :
    (serreConcreteCubeComplexFunctor A).map (simplexSubsetCubeDimensionIso.{u} I hI).hom ≫
      necklaceLambdaCell A (necklaceInSimplexSubset I hI) = simplexSubsetLambdaCell A I hI := by
  have ht := (cubicalSerreChainsCubeIso A).hom.naturality
    (simplexSubsetCubeDimensionIso.{u} I hI).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cubicalSerreChains A).map
      (necklaceCubicalCell (necklaceInSimplexSubset I hI))) ht).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f)
          ((cubicalSerreChains A).map_comp _ _).symm)))

/-- 元の左右分割の実射は、元の同じ端点の Serre 生成射を回収する。 -/
lemma simplexSubsetSplitLambdaCell_relation {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (serreConcreteCubeComplexFunctor A).map
        (necklaceConcreteCubeMap (simplexSubsetSplitRefinement.{u} I j hj hL hR)) ≫
      necklaceLambdaCell A (necklaceInSimplexSubset I hI) =
        necklaceLambdaCell A (necklaceInSimplexSubsetSplit I hI j hj hL hR) :=
  necklaceLambdaCell_relation A (necklaceInSimplexSubsetSplitInclusion I hI j hj hL hR)

/-- 元の共有座標の標準鎖一面は、元の左右分割の Serre 生成射を同じ Hom 内で回収する。 -/
lemma simplexSubsetSplitLambdaCell_one_face {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (serreConcreteCubeComplexFunctor A).map
        (necklaceWedgeBeadRefinementFace.{u} ((I.filter (· ≤ j)).card - 1)
          ((I.filter (j ≤ ·)).card - 1) (by omega) (by omega)) ≫
      (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single k).dimension)
          (simplexSubsetSplit_length I j hj hL hR))).hom ≫
        necklaceLambdaCell A (necklaceInSimplexSubset I hI) =
      necklaceLambdaCell A (necklaceInSimplexSubsetSplit I hI j hj hL hR) := by
  have h := congrArg ((serreConcreteCubeComplexFunctor A).map)
    (simplexSubsetSplitRefinement_one_face.{u} I j hj hL hR)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ necklaceLambdaCell A (necklaceInSimplexSubset I hI))
      (((serreConcreteCubeComplexFunctor A).map_comp _ _).symm.trans h.symm)).trans
        (simplexSubsetSplitLambdaCell_relation A I hI j hj hL hR))

end SerrePositivity.KST.SConstruction
