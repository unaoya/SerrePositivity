module
public import SerrePositivity.KST.SConstruction.SerreCubeChainFace
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCellAtDimension
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaEraseFace

/-! # 元の同端点の部分集合生成射と指定次元の零面
概要：指定始域・終域で読む元の零面は、同じ削除部分集合の実生成射を回収する。
方針：元の濃度次元の零面定理と、元の次元移送との厳密な可換性を合成する。
規約：元の削除座標と実鎖射を保持。使われ方：読み替えの零端点再帰との一致。
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

/-- 元の同端点の部分集合生成射の零面は、濃度次元で同じ削除生成射を回収する。 -/
lemma simplexSubsetLambdaCellAt_zero_face :
    serreCubeChainFace A false ((I.erase j).card - 2) (I.card - 2)
        (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax) ≫
      simplexSubsetLambdaCellAt A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl =
    simplexSubsetLambdaCellAt A (I.erase j) (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (simplexSubsetErase_two I hI j hmin hmax)
      (simplexSubsetErase_min I hI j hmin hmax).symm
      (simplexSubsetErase_max I hI j hmin hmax).symm := by
  have h := simplexSubsetLambdaErase_zero_face I hI j hj hmin hmax A
  rw [serreCubeComplexMap_dimension_inv] at h
  change ((serreCubeFace A false ((I.erase j).card - 2)
      (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax)
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax))).hom ≫
    eqToHom (congrArg (serreCubeComplex A)
      (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm)) ≫
        simplexSubsetLambdaCell A I hI = _
  rw [Category.assoc]
  exact h

/-- 元の零面は、任意の同じ指定次元で削除部分集合の同端点生成射を回収する。 -/
lemma simplexSubsetLambdaCellAtDimension_zero_face (p q : ℕ)
    (hp : p = (I.erase j).card - 2) (hq : q = I.card - 2) (hc : p + 1 = q) :
    serreCubeChainFace A false p q hc
        (Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax)) ≫
      simplexSubsetLambdaCellAtDimension A I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl q hq =
    simplexSubsetLambdaCellAtDimension A (I.erase j) (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (simplexSubsetErase_two I hI j hmin hmax)
      (simplexSubsetErase_min I hI j hmin hmax).symm
      (simplexSubsetErase_max I hI j hmin hmax).symm p hp := by
  unfold simplexSubsetLambdaCellAtDimension
  rw [← Category.assoc, serreCubeChainFace_naturality A false hp hq
    (simplexSubsetErase_normalized_codimension I hI j hj hmin hmax).symm hc,
    Category.assoc, simplexSubsetLambdaCellAt_zero_face]

/-- 元の零面の式は、元の同じ端点を明示した指定次元の生成射でも厳密に成り立つ。 -/
lemma simplexSubsetLambdaCellAtDimension_zero_face_at (a b : Fin (n + 1))
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (p q : ℕ) (hp : p = (I.erase j).card - 2) (hq : q = I.card - 2) (hc : p + 1 = q) :
    serreCubeChainFace A false p q hc
        (Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax)) ≫
      simplexSubsetLambdaCellAtDimension A I a b hI ha hb q hq =
    simplexSubsetLambdaCellAtDimension A (I.erase j) a b
      (simplexSubsetErase_two I hI j hmin hmax)
      (ha.trans (simplexSubsetErase_min I hI j hmin hmax).symm)
      (hb.trans (simplexSubsetErase_max I hI j hmin hmax).symm) p hp := by
  subst a b
  exact simplexSubsetLambdaCellAtDimension_zero_face A I hI j hj hmin hmax p q hp hq hc

end SerrePositivity.KST.SConstruction
