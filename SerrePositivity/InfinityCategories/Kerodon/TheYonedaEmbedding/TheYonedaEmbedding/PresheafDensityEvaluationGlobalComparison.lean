module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafDensityEvaluationRestrictionBase
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafDensityLiftedEvaluation

/-!
概要：評価密度変換の実際の像を、同じ始点固定の全族上で元の大域評価へ比較する。
方針：同じ評価復元射への相対前合成と、元の実現射との合成公式を使う。
規約：比較全体を同じ底上の相対 Hom 内に保つ。
使われ方：native 密度 fiber 写像を元の始点固定評価の弱同値へ接続する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsHomDiagram p
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsTargetDiagram F
local notation "Dx" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationDiagram F x
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationVertex F x

/-- 同じ評価変換の実際の像は、同じ復元射上で元の大域評価と相対的に同型。 -/
def presheafDensityEvaluationGlobalComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationReconstructionPre F x).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap Dx (SSet.const z) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationRelativeTargetMap F x).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluatedTransformationVertex F x)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationGlobalPre F x).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G)
          ((SSet.uliftFunctor.{u + 1, u}).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsReconstruction p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection H))
          ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsMap F) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso G).hom) (by
              rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection, ← Functor.map_comp,
                _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsMap_projection,
                _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsReconstruction_projection]))) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationRelativeImageIso F x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationReconstructionPre F x)
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityLiftedEvaluationIso F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationGlobalPre F x)
  refine he ≪≫ ?_ ≪≫ hf
  apply eqToIso
  apply congrArg HomotopyCategory.mk
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationReconstructionLift F x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap Dx H
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion F x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion_source F x) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentRealizationLargeMap H G (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityTransformation F).map) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison p x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsReconstruction p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityTransformation F).map) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso G).hom)
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationReconstruction_realization F x)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
