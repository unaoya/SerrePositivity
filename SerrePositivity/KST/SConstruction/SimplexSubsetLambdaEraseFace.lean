module
public import SerrePositivity.KST.SConstruction.SimplexSubsetEraseNormalizedFace
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaInclusion

/-! # 元の HA 用 Serre 生成射の削除零面
概要：元の濃度−2 次元の標準鎖零面との合成は、同じ端点の削除部分集合の生成射を回収。
方針：元の正規化した実 cube 包含を零面で分解し、元の Serre 関手と生成射比較を使う。
規約：元の次元同型の逆だけで次数を揃える。使われ方：native HA の削除項の実照合。
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

/-- 元の次元を揃えた削除の実 cube 包含は、元の標準零面と元の逆次元移送の合成。 -/
lemma simplexSubsetErase_cube_factor :
    simplexSubsetCubeInclusion.{u} (I.erase j) I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (simplexSubsetErase_two I hI j hjm hjM) hI
        (Finset.erase_subset _ _) (simplexSubsetErase_min I hI j hjm hjM).symm
        (simplexSubsetErase_max I hI j hjm hjM).symm rfl rfl =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace false ((I.erase j).card - 2)
        (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
          (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM)) ≫
      (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
        (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
        (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).inv :=
  (Iso.eq_comp_inv _).mpr (simplexSubsetErase_normalized_zero_face.{u} I hI j hj hjm hjM)

/-- 元の HA 用の同じ Serre 生成射の零面は、元の削除部分集合の同端点の生成射を回収する。 -/
lemma simplexSubsetLambdaErase_zero_face (A : Type u) [CommRing A] :
    (serreCubeFace A false ((I.erase j).card - 2)
        (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
          (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM))).hom ≫
      (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
          (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).inv ≫
        simplexSubsetLambdaCell A I hI =
    simplexSubsetLambdaCellAt A (I.erase j) (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (simplexSubsetErase_two I hI j hjm hjM)
      (simplexSubsetErase_min I hI j hjm hjM).symm
      (simplexSubsetErase_max I hI j hjm hjM).symm := by
  have hf := congrArg (fun f => f.hom) (serreConcreteCubeMap_face A false ((I.erase j).card - 2)
    (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
      (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM)))
  have h := congrArg ((serreConcreteCubeComplexFunctor A).map)
    (simplexSubsetErase_cube_factor.{u} I hI j hj hjm hjM)
  have hs := simplexSubsetLambdaCellAt_inclusion A (I.erase j) I
    (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (simplexSubsetErase_two I hI j hjm hjM) hI (Finset.erase_subset _ _)
    (simplexSubsetErase_min I hI j hjm hjM).symm
    (simplexSubsetErase_max I hI j hjm hjM).symm rfl rfl
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ simplexSubsetLambdaCell A I hI)
      ((congrArg (fun f => f ≫ (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
          (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).inv) hf.symm).trans
        (((serreConcreteCubeComplexFunctor A).map_comp _ _).symm.trans h.symm))).trans hs)

end SerrePositivity.KST.SConstruction
