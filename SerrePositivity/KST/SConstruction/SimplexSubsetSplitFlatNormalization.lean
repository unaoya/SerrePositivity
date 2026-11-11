module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitNormalizedLambda

/-! # 元の分割 cube の平坦次元と濃度次元
概要：元の左右 cube の次元和を、同じ元の削除部分集合の濃度次元と同定する。
方針：元の連結次元の加法性と、元の次元移送の推移を使う。
規約：元の tensor 比較・実 Serre 射を保持。使われ方：一面最高生成元の次元移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

include hI hj hjm hjM in
/-- 元の左右 cube の次元和は、元の削除部分集合の濃度から二を除いた値。 -/
lemma simplexSubsetSplit_flat_erase_dimension :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).dimension +
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1)).dimension = (I.erase j).card - 2 :=
  ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedge_dimension
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1))).symm.trans
      (simplexSubsetSplit_wedge_erase_dimension I hI j hj hjm hjM)

/-- 元の平坦次元への移送と元の tensor cube 比較は、元の濃度次元からの移送そのもの。 -/
lemma simplexSubsetSplit_source_triangle :
    (concreteCubeDimensionIso
      (simplexSubsetSplit_flat_erase_dimension I hI j hj hjm hjM).symm).hom ≫
      (necklaceCubeTensorIso (necklaceBead.{u} ((I.filter (· ≤ j)).card - 1))
        (necklaceBead ((I.filter (j ≤ ·)).card - 1))).hom =
    (concreteCubeDimensionIso
      (simplexSubsetSplit_wedge_erase_dimension I hI j hj hjm hjM).symm).hom :=
  concreteCubeDimensionIso_hom_trans
    (simplexSubsetSplit_flat_erase_dimension I hI j hj hjm hjM).symm
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedge_dimension
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1))).symm

/-- 元の標準鎖一面は、元の平坦 tensor 次元移送と実分割 Serre 生成射を回収する。 -/
lemma simplexSubsetLambdaSplit_flat_one_face (A : Type u) [CommRing A] :
    (serreCubeFace A true ((I.erase j).card - 2)
        (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
          (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM))).hom ≫
      (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
          (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).inv ≫
        simplexSubsetLambdaCell A I hI =
    (serreConcreteCubeComplexFunctor A).map (concreteCubeDimensionIso
      (simplexSubsetSplit_flat_erase_dimension I hI j hj hjm hjM).symm).hom ≫
      (serreConcreteCubeComplexFunctor A).map
        (necklaceCubeTensorIso (necklaceBead ((I.filter (· ≤ j)).card - 1))
          (necklaceBead ((I.filter (j ≤ ·)).card - 1))).hom ≫
        necklaceLambdaCell A (necklaceInSimplexSubsetSplit I hI j hj
          (simplexSubsetSplitLeft_two I hI j hj hjm)
          (simplexSubsetSplitRight_two I hI j hj hjM)) := by
  have h := congrArg ((serreConcreteCubeComplexFunctor A).map)
    (simplexSubsetSplit_source_triangle.{u} I hI j hj hjm hjM)
  exact (simplexSubsetLambdaSplit_normalized_one_face A I hI j hj hjm hjM).trans
    ((congrArg (fun f => f ≫ necklaceLambdaCell A (necklaceInSimplexSubsetSplit I hI j hj
      (simplexSubsetSplitLeft_two I hI j hj hjm) (simplexSubsetSplitRight_two I hI j hj hjM)))
      (h.symm.trans ((serreConcreteCubeComplexFunctor A).map_comp _ _))).trans
        (Category.assoc _ _ _))

end SerrePositivity.KST.SConstruction
