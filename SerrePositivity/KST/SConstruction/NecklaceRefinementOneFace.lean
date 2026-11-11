module
public import SerrePositivity.KST.SConstruction.NecklaceRefinementMissingCoordinate
public import SerrePositivity.KST.SConstruction.ConcreteCubeFaceCriterion
public import SerrePositivity.KST.SConstruction.SerreCubeDimensionTransport

/-! # 元の三 joint refinement と標準一面
概要：元の内部 joint が一つの実 refinement cube 射と Serre 射は、同じ座標の標準一面。
方針：元の全数値座標の順序・像・値と余次元一から面を判定し、元の関手を適用する。
規約：元の次元構造同型のみを使う。使われ方：分割合成項の標準鎖一面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (j : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).NonjointVertex)

/-- 元の三 joint refinement の実 cube 射は、元の中間 joint の同じ座標の標準一面。 -/
lemma necklaceRefinement_cube_one_face
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax}) :
    necklaceConcreteCubeMap (necklaceBeadRefinement T) ≫
        (concreteCubeDimensionIso
          (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension)
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1))
          (necklaceRefinementMissingCoordinate_codimension T j hJ)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true T.down.dimension
        (Fin.cast (necklaceRefinementMissingCoordinate_codimension T j hJ)
          (necklaceRefinementMissingCoordinate T j)) :=
  concreteCube_face_of_coordinate_embedding true _ (necklaceRefinementCoordinate T)
    (necklaceRefinementMissingCoordinate T j)
    (necklaceRefinementMissingCoordinate_codimension T j hJ)
    (necklaceRefinementMissingCoordinate_range T j hJ)
    (necklaceRefinementMissingCoordinate_one T j hJ) (necklaceRefinementCoordinate_numeric T)

/-- 元の三 joint refinement は、元の標準一面と同じ逆次元移送の合成。 -/
lemma necklaceRefinement_cube_factor
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax}) :
    necklaceConcreteCubeMap (necklaceBeadRefinement T) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true T.down.dimension
        (Fin.cast (necklaceRefinementMissingCoordinate_codimension T j hJ)
          (necklaceRefinementMissingCoordinate T j)) ≫
        (concreteCubeDimensionIso
          (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension)
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1))
          (necklaceRefinementMissingCoordinate_codimension T j hJ)).inv :=
  (Iso.eq_comp_inv _).mpr (necklaceRefinement_cube_one_face T j hJ)

/-- 元の三 joint refinement の同じ Serre 射は、元の次元移送後に同じ標準鎖一面。 -/
lemma necklaceRefinement_serre_one_face (A : Type u) [CommRing A]
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax}) :
    serreConcreteCubeMap A (necklaceConcreteCubeMap (necklaceBeadRefinement T)) ≫
        serreCubeDimensionMap A (necklaceRefinementMissingCoordinate_codimension T j hJ) =
      serreCubeFace A true T.down.dimension
        (Fin.cast (necklaceRefinementMissingCoordinate_codimension T j hJ)
          (necklaceRefinementMissingCoordinate T j)) := by
  have h := congrArg (fun f => serreConcreteCubeMap A f) (necklaceRefinement_cube_one_face T j hJ)
  exact (congrArg (fun f =>
    serreConcreteCubeMap A (necklaceConcreteCubeMap (necklaceBeadRefinement T)) ≫ f)
      (serreConcreteCubeMap_dimension A
        (necklaceRefinementMissingCoordinate_codimension T j hJ)).symm).trans
    ((serreConcreteCubeMap_comp A _ _).symm.trans
      (h.trans (serreConcreteCubeMap_face A true _ _)))

end SerrePositivity.KST.SConstruction
