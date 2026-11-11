module
public import SerrePositivity.KST.SConstruction.SimplexSubsetEraseCoordinates
public import SerrePositivity.KST.SConstruction.ConcreteCubeZeroFaceCriterion
public import SerrePositivity.KST.SConstruction.SerreCubeDimensionTransport

/-! # 元の内部点削除と標準の数値零面の厳密な一致
概要：元の内部点削除の cube 射は、元の右端座標の標準零面で、Serre 鎖でも同じ面。
方針：元の座標包含の順序・像と全座標値で零面を判定し、元の Serre 関手を適用する。
規約：元の次元構造同型だけを使用。使われ方：native HA 方程式の削除項。
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

/-- 元の内部点削除の実 cube 射は、元の同じ欠落数値座標の標準零面そのもの。 -/
lemma necklaceInSimplexSubsetErase_cube_zero_face :
    necklaceConcreteCubeMap (necklaceInSimplexSubsetErase.{u} I hI j hjm hjM).necklaceHom ≫
        (concreteCubeDimensionIso
          (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).dimension)
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk
            ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).dimension + 1))
          (simplexSubsetEraseCoordinate_codimension I hI j hj hjm hjM)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace false (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).dimension
        (Fin.cast (simplexSubsetEraseCoordinate_codimension I hI j hj hjm hjM)
          (simplexSubsetEraseCoordinate I hI j hj hjm hjM)) :=
  concreteCube_zero_face_of_coordinate_embedding _
    (simplexSubsetCoordinateInclusion (I.erase j) I (simplexSubsetErase_two I hI j hjm hjM) hI
      (Finset.erase_subset _ _) (simplexSubsetErase_min I hI j hjm hjM)
        (simplexSubsetErase_max I hI j hjm hjM))
    (simplexSubsetEraseCoordinate I hI j hj hjm hjM)
    (simplexSubsetEraseCoordinate_codimension I hI j hj hjm hjM)
    (simplexSubsetEraseCoordinate_range I hI j hj hjm hjM)
    (simplexSubsetEraseCoordinate_zero.{u} I hI j hj hjm hjM)
    (simplexSubsetCoordinateInclusion_numeric.{u} (I.erase j) I
      (simplexSubsetErase_two I hI j hjm hjM) hI (Finset.erase_subset _ _)
      (simplexSubsetErase_min I hI j hjm hjM) (simplexSubsetErase_max I hI j hjm hjM))

/-- 元の内部点削除の同じ Serre 射は、元の次元移送後に同じ標準鎖零面を回収する。 -/
lemma necklaceInSimplexSubsetErase_serre_zero_face (A : Type u) [CommRing A] :
    serreConcreteCubeMap A
        (necklaceConcreteCubeMap (necklaceInSimplexSubsetErase.{u} I hI j hjm hjM).necklaceHom) ≫
      serreCubeDimensionMap A (simplexSubsetEraseCoordinate_codimension I hI j hj hjm hjM) =
    serreCubeFace A false (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.erase j).card - 1)).dimension
      (Fin.cast (simplexSubsetEraseCoordinate_codimension I hI j hj hjm hjM)
        (simplexSubsetEraseCoordinate I hI j hj hjm hjM)) := by
  have h := congrArg (fun f => serreConcreteCubeMap A f)
    (necklaceInSimplexSubsetErase_cube_zero_face.{u} I hI j hj hjm hjM)
  exact (congrArg (fun f => serreConcreteCubeMap A
    (necklaceConcreteCubeMap (necklaceInSimplexSubsetErase.{u} I hI j hjm hjM).necklaceHom) ≫ f)
      (serreConcreteCubeMap_dimension A
        (simplexSubsetEraseCoordinate_codimension I hI j hj hjm hjM)).symm).trans
    ((serreConcreteCubeMap_comp A _ _).symm.trans
      (h.trans (serreConcreteCubeMap_face A false _ _)))

end SerrePositivity.KST.SConstruction
