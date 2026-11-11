module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitNormalizedComparison
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitLambdaCell

/-! # 元の濃度次元の標準一面の Serre 生成射
概要：元の削除零面と同じ座標の標準鎖一面から、元の分割 Serre 生成射を回収する。
方針：元の実分割 cube の可換三角形を Serre 関手に送り、元の表示関係を合成する。
規約：元の全体生成射・同じ端点・標準面を保持。使われ方：native HA の合成項の面表示。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

/-- 元の濃度次元の分割 cube は、元の同じ端点の実分割 Serre 生成射を回収する。 -/
lemma simplexSubsetSplitNormalizedCube_lambda :
    (serreConcreteCubeComplexFunctor A).map
        (simplexSubsetSplitNormalizedCube.{u} I hI j hj hjm hjM) ≫
      simplexSubsetLambdaCell A I hI =
    (serreConcreteCubeComplexFunctor A).map (concreteCubeDimensionIso
      (simplexSubsetSplit_wedge_erase_dimension I hI j hj hjm hjM).symm).hom ≫
      necklaceLambdaCell A (necklaceInSimplexSubsetSplit I hI j hj
        (simplexSubsetSplitLeft_two I hI j hj hjm)
        (simplexSubsetSplitRight_two I hI j hj hjM)) := by
  have hn := simplexSubsetLambdaCell_necklace A I hI
  have hc := congrArg ((serreConcreteCubeComplexFunctor A).map)
    (simplexSubsetSplitNormalizedCube_comparison.{u} I hI j hj hjm hjM)
  have hr := simplexSubsetSplitLambdaCell_relation A I hI j hj
    (simplexSubsetSplitLeft_two I hI j hj hjm) (simplexSubsetSplitRight_two I hI j hj hjM)
  exact (congrArg (fun f => (serreConcreteCubeComplexFunctor A).map
    (simplexSubsetSplitNormalizedCube.{u} I hI j hj hjm hjM) ≫ f) hn.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ necklaceLambdaCell A (necklaceInSimplexSubset I hI))
        (((serreConcreteCubeComplexFunctor A).map_comp _ _).symm.trans
          (hc.trans ((serreConcreteCubeComplexFunctor A).map_comp _ _)))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f => (serreConcreteCubeComplexFunctor A).map (concreteCubeDimensionIso
            (simplexSubsetSplit_wedge_erase_dimension I hI j hj hjm hjM).symm).hom ≫ f) hr))))

/-- 元の標準鎖一面から、元の同じ分割 Serre 生成射を濃度次元で回収する。 -/
lemma simplexSubsetLambdaSplit_normalized_one_face :
    (serreCubeFace A true ((I.erase j).card - 2)
        (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
          (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM))).hom ≫
      (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
          (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).inv ≫
        simplexSubsetLambdaCell A I hI =
    (serreConcreteCubeComplexFunctor A).map (concreteCubeDimensionIso
      (simplexSubsetSplit_wedge_erase_dimension I hI j hj hjm hjM).symm).hom ≫
      necklaceLambdaCell A (necklaceInSimplexSubsetSplit I hI j hj
        (simplexSubsetSplitLeft_two I hI j hj hjm)
        (simplexSubsetSplitRight_two I hI j hj hjM)) := by
  have hf := congrArg (fun f => f.hom) (serreConcreteCubeMap_face A true ((I.erase j).card - 2)
    (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
      (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM)))
  have hc := congrArg ((serreConcreteCubeComplexFunctor A).map)
    ((Iso.eq_comp_inv _).mpr (simplexSubsetSplit_normalized_one_face.{u} I hI j hj hjm hjM))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ simplexSubsetLambdaCell A I hI)
      ((congrArg (fun f => f ≫ (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
          (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).inv) hf.symm).trans
        (((serreConcreteCubeComplexFunctor A).map_comp _ _).symm.trans hc.symm))).trans
          (simplexSubsetSplitNormalizedCube_lambda A I hI j hj hjm hjM))

end SerrePositivity.KST.SConstruction
