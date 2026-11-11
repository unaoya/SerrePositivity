module
public import SerrePositivity.KST.SConstruction.SerreCubeChainCompositionComparison
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaSpecifiedOneFace

/-! # 元の標準一面の指定端点・次元
概要：元の一面と左右 necklace の実分割合成の比較を、指定した端点と次元へ移す。
方針：元の面の次元自然性で移送を前へ出し、同じ移送を異種等号で外す。
規約：元の鎖射全体と数値座標を保持。使われ方：読み替え次元の一面の特殊化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (hmin : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hmax : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

/-- 指定端点・次元の一面の実鎖射は、元の濃度次元の同じ一面と異種等号で一致。 -/
lemma simplexSubsetLambdaCellAtDimension_one_face_normalized_heq (a b : Fin (n + 1))
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (p q : ℕ) (hp : p = (I.erase j).card - 2) (hq : q = I.card - 2) (hc : p + 1 = q) :
    HEq (serreCubeChainFace A true p q hc
        (Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax)) ≫
      simplexSubsetLambdaCellAtDimension A I a b hI ha hb q hq)
      (serreCubeChainFace A true ((I.erase j).card - 2) (I.card - 2)
        (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax) ≫
      simplexSubsetLambdaCellAt A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl) := by
  subst a b
  have he : serreCubeChainFace A true p q hc
        (Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax)) ≫
      simplexSubsetLambdaCellAtDimension A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl q hq =
      eqToHom (congrArg (serreCubeComplex A) hp) ≫
        (serreCubeChainFace A true ((I.erase j).card - 2) (I.card - 2)
          (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm
          (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax) ≫
        simplexSubsetLambdaCellAt A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
          (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl) := by
    unfold simplexSubsetLambdaCellAtDimension
    rw [← Category.assoc, serreCubeChainFace_naturality A true hp hq
      (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm hc, Category.assoc]
  exact (heq_of_eq he).trans (serreCubeChain_precomp_heq A hp _)

/-- 元の指定端点・次元での一面は、元の左右 necklace の実分割合成を回収する。 -/
lemma simplexSubsetLambdaCellAtDimension_one_face_heq (a b : Fin (n + 1))
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (p q : ℕ) (hp : p = (I.erase j).card - 2) (hq : q = I.card - 2) (hc : p + 1 = q) :
    let T := necklaceInSimplexSubsetSplitLeft.{u} I hI j hj
      (simplexSubsetSplitLeft_two I hI j hj hmin)
    let U := necklaceInSimplexSubsetSplitRight.{u} I hI j hj
      (simplexSubsetSplitRight_two I hI j hj hmax)
    HEq (serreCubeChainFace A true p q hc
        (Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax)) ≫
      simplexSubsetLambdaCellAtDimension A I a b hI ha hb q hq)
      (serreCubeChainComposition A T.necklace.down.dimension U.necklace.down.dimension
        (necklaceLambdaCell A T) (necklaceLambdaCell A U)) := by
  exact (simplexSubsetLambdaCellAtDimension_one_face_normalized_heq A I hI j hj hmin hmax
    a b ha hb p q hp hq hc).trans (simplexSubsetLambdaCellAt_one_face_heq A I hI j hj hmin hmax)

end SerrePositivity.KST.SConstruction
