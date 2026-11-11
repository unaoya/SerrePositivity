module
public import SerrePositivity.KST.SConstruction.SerreCubeComplexDimensionComparison
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaSpecifiedFace
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitFlatNormalization
public import SerrePositivity.KST.SConstruction.NecklaceLambdaComposition

/-! # 元の標準一面と左右部分集合の実 tensor 合成
概要：指定始域・終域で読む元の一面は、左右部分集合の実 Serre 生成射の合成を回収。
方針：元の平坦分割一面の式と元の全 necklace の合成則を合成し、次元移送を外す。
規約：元の実鎖射全体を比較する。使われ方：読み替えの一端点の帰納的比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の同端点生成射の標準一面は、元の左右 necklace の実 tensor 分割合成。 -/
lemma simplexSubsetLambdaCellAt_one_face_heq {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hmin : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hmax : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    let T := necklaceInSimplexSubsetSplitLeft.{u} I hI j hj
      (simplexSubsetSplitLeft_two I hI j hj hmin)
    let U := necklaceInSimplexSubsetSplitRight.{u} I hI j hj
      (simplexSubsetSplitRight_two I hI j hj hmax)
    HEq (serreCubeChainFace A true ((I.erase j).card - 2) (I.card - 2)
        (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax) ≫
      simplexSubsetLambdaCellAt A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl)
      ((serreCubeTensorIso A T.necklace.down.dimension U.necklace.down.dimension).hom.hom ≫
        (necklaceLambdaCell A T ⊗ₘ necklaceLambdaCell A U) ≫
          eComp (C := CubicalLambda A (Δ[n] : SSet.{u})) (Complex A)
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j)
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))) := by
  let T := necklaceInSimplexSubsetSplitLeft.{u} I hI j hj
    (simplexSubsetSplitLeft_two I hI j hj hmin)
  let U := necklaceInSimplexSubsetSplitRight.{u} I hI j hj
    (simplexSubsetSplitRight_two I hI j hj hmax)
  let prod := (serreCubeTensorIso A T.necklace.down.dimension U.necklace.down.dimension).hom.hom ≫
    (necklaceLambdaCell A T ⊗ₘ necklaceLambdaCell A U) ≫
      eComp (Complex A) (C := CubicalLambda A (Δ[n] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
  have hc := necklaceLambdaCell_composition A T U
  have h := simplexSubsetLambdaSplit_flat_one_face I hI j hj hmin hmax A
  rw [serreCubeComplexMap_dimension_inv] at h
  have hn : serreCubeChainFace A true ((I.erase j).card - 2) (I.card - 2)
      (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm
      (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax) ≫
      simplexSubsetLambdaCellAt A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl =
      (serreConcreteCubeComplexFunctor A).map (concreteCubeDimensionIso
        (simplexSubsetSplit_flat_erase_dimension I hI j hj hmin hmax).symm).hom ≫ prod := by
    change ((serreCubeFace A true ((I.erase j).card - 2)
      (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax)
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax))).hom ≫
      eqToHom (congrArg (serreCubeComplex A)
        (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm)) ≫
          simplexSubsetLambdaCell A I hI = _
    rw [Category.assoc]
    exact h.trans (congrArg (fun f => (serreConcreteCubeComplexFunctor A).map
      (concreteCubeDimensionIso
        (simplexSubsetSplit_flat_erase_dimension I hI j hj hmin hmax).symm).hom ≫ f) hc.symm)
  exact (heq_of_eq hn).trans (serreCubeComplex_dimension_precomp_heq A
    (simplexSubsetSplit_flat_erase_dimension I hI j hj hmin hmax).symm prod)

end SerrePositivity.KST.SConstruction
