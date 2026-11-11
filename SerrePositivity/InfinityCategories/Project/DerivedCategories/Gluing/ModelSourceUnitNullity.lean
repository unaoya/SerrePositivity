module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelSourceTetrahedronFaceAgreement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TerminalUnitLoopClass
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTetrahedronLoopDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelUnitProjectionNullity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelSourceUnitFace
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter R C D M X Y

lemma dgGluingModelLeftUnitLoop_class :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelLeftUnitLoop R C D M X Y)) = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelLeftUnitLoop_class_of_unit_face R C D M X Y
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitProjectionTetrahedron_source_unit_face R C D M X Y)

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling_of_target_unit_face
    (hR : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitProjectionTetrahedron R C D M X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)) :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary_filling_of_projection_unit_faces R C D M X Y hR
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitProjectionTetrahedron_source_unit_face R C D M X Y)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
