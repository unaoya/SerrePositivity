module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalBoundaryFamilyNaturality

/-!
概要：区間上の元の全空間の両端写像を固定した実際の分類区間族。
方針：元の二つの fiber の包含と普遍区間を相対データに束ねる。
規約：区間内部の分類図式は全て動かす。
使われ方：円柱の可縮な境界 fiber を表現空間へ移す区間側の空間。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：元の全空間の共通境界の左成分は区間の零端へ写る。
方針：始点 fiber の包含の射影条件。
規約：p の充填性は不要。
使われ方：実際の区間データの左端条件。 -/
lemma intervalFiberBoundary_zero {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFiberEndpointInclusion p) ≫ p =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫ p = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _

/-- 概要：元の全空間の共通境界の右成分は区間の一端へ写る。
方針：終点 fiber の包含の射影条件。
規約：p の充填性は不要。
使われ方：実際の区間データの右端条件。 -/
lemma intervalFiberBoundary_one {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFiberEndpointInclusion p) ≫ p =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫ p = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _

/-- 概要：元の全空間の両端と分類図式の相対内部 Hom。
方針：両端 fiber の包含に対する相対内部 Hom を取る。
規約：p の fibration 性は要求しない。
使われ方：元の区間上の全空間の境界固定 lift 空間。 -/
def intervalBoundaryRelativeHom {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) :
    internalHom.PullbackObjObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFiberEndpointInclusion p) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection :=
  Functor.PullbackObjObj.ofHasPullback internalHom _ _

/-- 概要：元の全空間の両端写像を固定した実際の区間族データ。
方針：二つの fiber 写像と普遍区間を相対データへ束ねる。
規約：両端写像に同値性はまだ要求しない。
使われ方：表現空間の境界 fiber の concrete な模型。 -/
def intervalFixedBoundaryFamilyData {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
    (g₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s)
    (g₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t ⟶
        (intervalBoundaryRelativeHom p).pt :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryFamilyData p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFiberEndpointInclusion p)
    (intervalFiberBoundary_zero p) (intervalFiberBoundary_one p)
    (intervalBoundaryRelativeHom p) g₀ g₁

/-- 概要：元の全空間上で両端写像を固定し内部の分類区間を動かす全 lift 空間。
方針：実際の区間データへ相対内部 Hom を引き戻す。
規約：元の全空間の全高次 lift を含む。
使われ方：区間の表現空間の境界 fiber と同定する空間。 -/
def intervalFixedBoundaryFamilySpace {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
    (g₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s)
    (g₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace (intervalBoundaryRelativeHom p)
    (intervalFixedBoundaryFamilyData p g₀ g₁)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
