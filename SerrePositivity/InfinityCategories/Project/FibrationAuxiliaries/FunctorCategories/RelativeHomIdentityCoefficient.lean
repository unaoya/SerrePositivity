module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedReverseFiberVertices
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomPointedNaturality

/-!
概要：相対恒等射の pointed 頂点を、同じ輸送族の標準一点 Hom 係数として表す。
方針：恒等射の点を Yoneda の射に直し、反転した一点 Hom 比較の頂点計算を使う。
規約：既存の pointed 恒等点そのものと厳密に一致させる。
使われ方：Hom 関手の大域比較の fiber 作用に、相対合成の単位則を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 相対恒等射の点を指定する、一点 Kan 空間から自己 Hom への実際の射。 -/
def relativeHomIdentityPointMap {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject ⟶ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityKanObject q :=
  SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app (Opposite.op ⦋0⦌) PUnit.unit)

/-- 同じ恒等点を、輸送に使う反転した一点 Hom の零単体として表す。 -/
def relativeHomIdentityCoefficient {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityKanObject q))).op) _⦋0⦌ :=
  SSet.opObjEquiv.symm (ULift.up
    (SimplicialCategory.homEquiv' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityKanObject q)
      (relativeHomIdentityPointMap q)))

/-- 実際の fiber 比較は、この係数を既存の相対恒等射の pointed 頂点へ厳密に送る。 -/
lemma relativeHomIdentityCoefficient_pointed {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityKanObject q)).app
      (Opposite.op ⦋0⦌) (relativeHomIdentityCoefficient q) = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomPointedIdentity q := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityKanObject q)).injective
  calc
    _ = SSet.yonedaEquiv (relativeHomIdentityPointMap q) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison_vertex (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityKanObject q)
        (relativeHomIdentityPointMap q)
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app (Opposite.op ⦋0⦌) PUnit.unit :=
      SSet.yonedaEquiv.apply_symm_apply _
    _ = _ := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomPointedIdentity_value q).symm

/-- 任意のパラメーター全体で、同じ恒等係数の像は元の pointed 恒等点の定値族。 -/
lemma relativeHomIdentityCoefficient_family {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)
    (P : SSet.{u + 1}) :
    (SSet.const (relativeHomIdentityCoefficient q) : P ⟶ _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityKanObject q) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomPointedIdentity q) := by
  rw [SSet.const_comp]
  exact congrArg (fun z ↦ (SSet.const z : P ⟶ _)) (relativeHomIdentityCoefficient_pointed q)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
