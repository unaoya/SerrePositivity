module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityRestrictedGlobalMap

/-!
概要：密度評価変換の実際の像を、同じ定値標的で元の制限大域評価へ比較する。
方針：全体側で構成済みの相対同型を、底変換の厳密な相対 Hom 同型で反映する。
規約：元の評価復元射・元の変換・元の大域評価を保持する。
使われ方：同じ指定値への fiber 写像の同型を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "Dx" => presheafDensityEvaluationDiagram F x
local notation "z" => presheafDensityEvaluationVertex F x

/-- 元の評価変換の像を同じ復元射へ制限すると、元の大域評価の同じ定値標的への制限と同型。 -/
def presheafDensityEvaluationConstantComparisonIso :
    VertexIso
      ((presheafDensityEvaluationConstantPre F x).app (Opposite.op ⦋0⦌)
        ((leftUnstraighteningMappingSpaceMap Dx (SSet.const z)).app (Opposite.op ⦋0⦌)
          (presheafDensityEvaluatedTransformationVertex F x)))
      (relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z))
        (presheafDensityEvaluationSourceBase F x) (presheafDensityRestrictedGlobalMap F x)
        (presheafDensityRestrictedGlobalMap_projection F x)) := by
  apply (qCatEquivalenceOfIso (presheafDensityEvaluationFixedTargetIso F x)).isFullyFaithful
    |>.preimageVertexIso
  have hs := presheafDensityEvaluationFixedTargetIso_source_vertex F x
    ((leftUnstraighteningMappingSpaceMap Dx (SSet.const z)).app (Opposite.op ⦋0⦌)
      (presheafDensityEvaluatedTransformationVertex F x))
  refine eqToIso (congrArg HomotopyCategory.mk hs) ≪≫
    presheafDensityEvaluationGlobalComparisonIso F x ≪≫ ?_
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  apply Subtype.ext
  change functorVertex
    ((SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (presheafTwistedElementsMap F) ≫
        (smallLeftUnstraighteningIso G).hom) =
    functorVertex (presheafDensityRestrictedGlobalMap F x ≫
      leftUnstraighteningMap (SSet.const z) G
        ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
        (presheafDensitySourceInclusion_target F x))
  rw [presheafTwistedElementsMap_lifted, presheafDensityRestrictedGlobalMap_map]

end SerrePositivity.InfinityCategories.F2.Ind
