module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelSourceTetrahedronFaceAgreement
public import SerrePositivity.InfinityCategories.Derived.Gluing.TerminalUnitLoopClass
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitTetrahedronLoopDiagonal
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitProjectionNullity
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelSourceUnitFace
/-!
概要：第一単位面を無条件に接続し、主経路の左単位閉路の零性を得る。
方針：元四面体の σ₀ 退化と二つの終側面の一致を相対内角比較へ代入する。
規約：同じ全入力を固定し、残る第二単位面だけを境界充填の明示入力とする。
使われ方：D-13 の全三角形退化を③の相対比較から④へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "K" => dgGluingModelUnitCollarParameter R C D M X Y

lemma dgGluingModelLeftUnitLoop_class :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingModelLeftUnitLoop R C D M X Y)) = 𝟙 _ :=
  dgGluingModelLeftUnitLoop_class_of_unit_face R C D M X Y
    (dgGluingModelUnitProjectionTetrahedron_source_unit_face R C D M X Y)

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling_of_target_unit_face
    (hR : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        intervalMappingUncurry (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)) :
    ∃ V, (boundary 2).ι ≫ V = dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y :=
  dgGluingLaxHomDiagonalComparisonBoundary_filling_of_projection_unit_faces R C D M X Y hR
    (dgGluingModelUnitProjectionTetrahedron_source_unit_face R C D M X Y)
end SerrePositivity.InfinityCategories
