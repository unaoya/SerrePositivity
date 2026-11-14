module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomTargetPointedDisplay
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeHomSpaceComparison
/-!
概要：同じ Hom 単位の実 pointed 表示を、公開済みの半自由 Hom 関手族へ接続する。
方針：二つの全関手が厳密に同じことを確認し、同じ射影と実 fiber 射を公開する。
規約：全 fiber の同値性は別工程。使われ方：元の F1 Hom 関手族との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 一般の構成は、公開済みの同じ半自由 Hom の空間値全関手そのもの。 -/
lemma dgHomTargetUnderlyingSpaceInfinity_semifree (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) P =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetSpaceInfinity R D P := by
  rfl
/-- 元の同じ半自由 Hom の実 coslice 全体からの pointed 表示。 -/
def dgSemifreeHomTargetCoslicePointedDisplay (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) P) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) P
/-- 同じ pointed 表示の底は、公開済みの同じ全空間値 Hom 関手。 -/
lemma dgSemifreeHomTargetCoslicePointedDisplay_projection (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    dgSemifreeHomTargetCoslicePointedDisplay R D P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P))) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetSpaceInfinity R D P := by
  rw [dgSemifreeHomTargetCoslicePointedDisplay, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_projection,
    dgHomTargetUnderlyingSpaceInfinity_semifree]
/-- 同じ全比較が誘導する、各指定終点上の実 fiber 射。 -/
def dgSemifreeHomTargetCoslicePointedFiber (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D P)))) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (dgSemifreeHomTargetCoslicePointedDisplay R D P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetSpaceInfinity R D P)
    (dgSemifreeHomTargetCoslicePointedDisplay_projection R D P)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D Q))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
