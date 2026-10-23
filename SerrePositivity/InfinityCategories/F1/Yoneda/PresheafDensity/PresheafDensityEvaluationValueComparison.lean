module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationConstantComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantUnstraighteningValueOverPre
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTargetVertex

/-!
概要：同じ密度評価の実際の fiber 値写像を、元の制限大域評価の値写像へ比較する。
方針：同じ定値標的内の相対同型を、既存の値への比較で写す。
規約：同じ評価復元射・指定値・元の実際の fiber 写像を保つ。
使われ方：元の始点固定評価の弱同値を native 密度余錐へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "Dx" => presheafDensityEvaluationDiagram F x
local notation "z" => presheafDensityEvaluationVertex F x
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor (twistedSourceElements p x)

/-- 同じ始点固定の元の大域評価を、同じ指定値への写像として読む。 -/
def presheafDensityRestrictedGlobalValueMap :=
  presheafDensityRestrictedGlobalMap F x ≫
    F2.constantUnstraighteningFiberProjection
      ((SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F)) z ≫
        (pointedSpaceFiberValueEquivalence z).hom

/-- 同じ相対 Hom の全変換を、同じ指定値への全空間写像に写す。 -/
def presheafDensityEvaluationConstantValueMap :=
  (F2.constantUnstraighteningRelativeIso (presheafDensityEvaluationSourceBase F x) z).hom ≫
    (ihom A).map (pointedSpaceFiberValueEquivalence z).hom

/-- 元の評価変換の実際の fiber 値写像は、同じ復元射上で元の制限大域評価と関手同型。 -/
def presheafDensityEvaluationValueComparisonIso :
    FunctorIso (presheafDensityEvaluationReconstructionLift F x ≫
      presheafDensityEvaluatedFiberMap F x) (presheafDensityRestrictedGlobalValueMap F x) := by
  have he := VertexIso.map (presheafDensityEvaluationConstantComparisonIso F x)
    (presheafDensityEvaluationConstantValueMap F x)
  have hs := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    ((leftUnstraighteningMappingSpaceMap Dx (SSet.const z)).app (Opposite.op ⦋0⦌)
      (presheafDensityEvaluatedTransformationVertex F x)))
    (F2.constantUnstraighteningRelativeIso_value_overPre (leftUnstraighteningProjection Dx)
      (presheafDensityEvaluationSourceBase F x) (presheafDensityEvaluationReconstructionLift F x)
      (presheafDensityEvaluationReconstructionLift_projection F x) z)
  change (presheafDensityEvaluationConstantValueMap F x).app (Opposite.op ⦋0⦌)
    ((presheafDensityEvaluationConstantPre F x).app (Opposite.op ⦋0⦌)
      ((leftUnstraighteningMappingSpaceMap Dx (SSet.const z)).app (Opposite.op ⦋0⦌)
        (presheafDensityEvaluatedTransformationVertex F x))) =
    ((pre (presheafDensityEvaluationReconstructionLift F x)).app _).app (Opposite.op ⦋0⦌)
      ((F2.coherentConstantTargetMap Dx z).app (Opposite.op ⦋0⦌)
        (presheafDensityEvaluatedTransformationVertex F x)) at hs
  rw [← presheafDensityEvaluatedFiberMap_vertex] at hs
  refine eqToIso (congrArg HomotopyCategory.mk hs.symm) ≪≫ he ≪≫ ?_
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  change ((ihom A).map (pointedSpaceFiberValueEquivalence z).hom).app (Opposite.op ⦋0⦌)
    ((F2.constantUnstraighteningRelativeIso (presheafDensityEvaluationSourceBase F x) z).hom.app _
      (relativeFunctorVertex _ _ (presheafDensityRestrictedGlobalMap F x)
        (presheafDensityRestrictedGlobalMap_projection F x))) = _
  rw [F2.constantUnstraighteningRelativeIso_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
