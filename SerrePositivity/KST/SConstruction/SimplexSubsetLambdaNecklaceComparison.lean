module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitLambdaCell
public import SerrePositivity.KST.SConstruction.SerreCubeComplexDimensionComparison

/-! # 元の部分集合 Serre 生成射と実 necklace 生成射
概要：同じ部分集合の指定端点の necklace 生成射と濃度次元の生成射を比較する。
方針：元の次元構造射を前合成した回収式から、同じ移送を異種等号で外す。
規約：元の実鎖射を保持。使われ方：分割一面の左右生成射の読み替え次元への比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の部分集合の濃度次元の実生成射は、元の同じ necklace 生成射と異種等号で一致。 -/
lemma simplexSubsetLambdaCell_necklace_heq {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) :
    HEq (simplexSubsetLambdaCell A I hI)
      (necklaceLambdaCell A (necklaceInSimplexSubset.{u} I hI)) := by
  have h := simplexSubsetLambdaCell_necklace A I hI
  have ht : HEq ((serreConcreteCubeComplexFunctor A).map
      (simplexSubsetCubeDimensionIso.{u} I hI).hom ≫
        necklaceLambdaCell A (necklaceInSimplexSubset I hI))
      (necklaceLambdaCell A (necklaceInSimplexSubset I hI)) :=
    serreCubeComplex_dimension_precomp_heq A (necklaceInSimplexSubset_dimension.{u} I hI).symm _
  exact (heq_of_eq h.symm).trans ht

/-- 元の指定端点の necklace 生成射は、同じ部分集合の濃度次元の実生成射に戻る。 -/
lemma necklaceLambdaCell_subsetAt_canonical_heq {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    HEq (necklaceLambdaCell A (necklaceInSimplexSubsetAt.{u} I a b hI ha hb))
      (simplexSubsetLambdaCell A I hI) := by
  subst a b
  exact (simplexSubsetLambdaCell_necklace_heq A I hI).symm

end SerrePositivity.KST.SConstruction
