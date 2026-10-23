module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationRestrictionBase
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityLiftedEvaluation

/-!
概要：評価密度変換の実際の像を、同じ始点固定の全族上で元の大域評価へ比較する。
方針：同じ評価復元射への相対前合成と、元の実現射との合成公式を使う。
規約：比較全体を同じ底上の相対 Hom 内に保つ。
使われ方：native 密度 fiber 写像を元の始点固定評価の弱同値へ接続する。
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
local notation "H" => twistedElementsHomDiagram p
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "Dx" => presheafDensityEvaluationDiagram F x
local notation "z" => presheafDensityEvaluationVertex F x

/-- 同じ評価変換の実際の像は、同じ復元射上で元の大域評価と相対的に同型。 -/
def presheafDensityEvaluationGlobalComparisonIso :
    VertexIso
      ((presheafDensityEvaluationReconstructionPre F x).app (Opposite.op ⦋0⦌)
        ((leftUnstraighteningMappingSpaceMap Dx (SSet.const z) ≫
          presheafDensityEvaluationRelativeTargetMap F x).app (Opposite.op ⦋0⦌)
            (presheafDensityEvaluatedTransformationVertex F x)))
      ((presheafDensityEvaluationGlobalPre F x).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection G)
          ((SSet.uliftFunctor.{u + 1, u}).map
            (twistedElementsReconstruction p ≫ smallLeftUnstraighteningProjection H))
          ((SSet.uliftFunctor.{u + 1, u}).map (presheafTwistedElementsMap F) ≫
            (smallLeftUnstraighteningIso G).hom) (by
              rw [Category.assoc, smallLeftUnstraighteningIso_projection, ← Functor.map_comp,
                presheafTwistedElementsMap_projection,
                twistedElementsReconstruction_projection]))) := by
  have he := VertexIso.map (presheafDensityEvaluationRelativeImageIso F x)
    (presheafDensityEvaluationReconstructionPre F x)
  have hf := VertexIso.map (presheafDensityLiftedEvaluationIso F)
    (presheafDensityEvaluationGlobalPre F x)
  refine he ≪≫ ?_ ≪≫ hf
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  apply Subtype.ext
  change functorVertex
    (presheafDensityEvaluationReconstructionLift F x ≫ leftUnstraighteningMap Dx H
      ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
      (presheafDensitySourceInclusion_source F x) ≫
        coherentRealizationLargeMap H G (presheafDensityTransformation F).map) =
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (twistedElementsReconstruction p ≫ (presheafDensityTransformation F).map) ≫
          (smallLeftUnstraighteningIso G).hom)
  exact congrArg functorVertex (presheafDensityEvaluationReconstruction_realization F x)

end SerrePositivity.InfinityCategories.F2.Ind
