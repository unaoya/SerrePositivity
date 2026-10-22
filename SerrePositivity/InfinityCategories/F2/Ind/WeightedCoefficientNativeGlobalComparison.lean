module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeRestrictionBase
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityLiftedEvaluation

/-!
概要：元の native 評価余錐の実際の像を、同じ始点固定族上で元の全評価へ相対比較する。
方針：native 復元での相対制限、元の共同実現射の合成公式、元の全評価同型を合成する。
規約：元の余錐・復元射・全評価を保持。使われ方：実際の評価 fiber 値写像の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "H" => twistedElementsHomDiagram (weightedDensityProjection F)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 元の native 評価余錐が定める、元の図式・頂点での標準変換頂点。 -/
def weightedCoefficientNativeCoconeTransformationVertex :=
  (F2.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
    (F2.coconeMappingPointAt (weightedCoefficientNativeEvaluationCocone κ F hF i x) z
      (weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x))

/-- 同じ native 評価余錐の実際の像は、同じ復元射上で元の全評価と相対的に同型。 -/
def weightedCoefficientNativeGlobalComparisonIso : VertexIso
    ((weightedCoefficientNativeReconstructionPre κ F i x).app (Opposite.op ⦋0⦌)
      ((leftUnstraighteningMappingSpaceMap D (SSet.const z) ≫
        weightedCoefficientNativeRelativeTargetMap κ F hF i x).app (Opposite.op ⦋0⦌)
          (weightedCoefficientNativeCoconeTransformationVertex κ F hF i x)))
    ((weightedCoefficientNativeGlobalPre F i x).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection G)
        ((SSet.uliftFunctor.{u + 1, u}).map
          (twistedElementsReconstruction (weightedDensityProjection F) ≫
            smallLeftUnstraighteningProjection H))
        ((SSet.uliftFunctor.{u + 1, u}).map (weightedDensityTwistedJointMap F) ≫
          (smallLeftUnstraighteningIso G).hom) (by
            rw [Category.assoc, smallLeftUnstraighteningIso_projection,
              ← CategoryTheory.Functor.map_comp, weightedDensityTwistedJointMap_projection,
              twistedElementsReconstruction_projection]))) := by
  have he := (weightedCoefficientNativeCoconeRelativeImageIso κ F hF i x).map
    (weightedCoefficientNativeReconstructionPre κ F i x)
  have hf := (weightedDensityLiftedEvaluationIso F).map (weightedCoefficientNativeGlobalPre F i x)
  refine he ≪≫ ?_ ≪≫ hf
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  apply Subtype.ext
  change functorVertex
    (weightedCoefficientNativeReconstructionLift κ F i x ≫
      leftUnstraighteningMap D H k (weightedCoefficientNativeEvaluationBase_source κ F i x) ≫
        coherentRealizationLargeMap H G (weightedDensityTransformation F).map) =
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceIntoTotal F i x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (twistedElementsReconstruction (weightedDensityProjection F) ≫
          (weightedDensityTransformation F).map) ≫ (smallLeftUnstraighteningIso G).hom)
  exact congrArg functorVertex (weightedCoefficientNativeReconstruction_realization κ F i x)

end SerrePositivity.InfinityCategories.F2.Ind
