module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafDensityEvaluationFixedTarget

/-!
概要：元の大域 pointed 評価を同じ始点固定の全族で制限し、同じ定値標的へ持ち上げる。
方針：元の pointed 成分と終点成分を引き戻しに入れ、全体への射を両成分で照合する。
規約：元の評価・指定値・同じ全族を保持する。
使われ方：密度の評価変換の像を元の始点固定評価と比較する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsTargetDiagram F
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationVertex F x

/-- 同じ始点固定の全族の共同射影は、指定された全体側の底そのもの。 -/
lemma presheafDensityRestrictedGlobalBase :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationSourceBase F x ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion F x) =
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison p x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsProjection p) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationGlobalBase, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsReconstruction_projection]
    using _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationSourceBase_global F x

/-- 元の pointed 評価の同じ制限は、同じ定値標的を被覆する。 -/
lemma presheafDensityRestrictedGlobalMap_over :
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison p x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsEvaluation F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationSourceBase F x ≫ (SSet.const z) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsEvaluation_over, ← Category.assoc,
    ← presheafDensityRestrictedGlobalBase, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion_target]

/-- 元の大域評価の始点固定を、同じ評価の定値 unstraightening へ戻す。 -/
def presheafDensityRestrictedGlobalMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElements p x) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (SSet.const z :
        (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :=
  pullback.lift
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison p x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsEvaluation F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationSourceBase F x)
    (presheafDensityRestrictedGlobalMap_over F x)

/-- 同じ制限評価は、元の終点の全空間への射影を保つ。 -/
lemma presheafDensityRestrictedGlobalMap_projection :
    presheafDensityRestrictedGlobalMap F x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (SSet.const z) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationSourceBase F x := pullback.lift_snd _ _ _

/-- 同じ制限評価を元の大域標的へ戻すと、元の大域評価の同じ制限。 -/
lemma presheafDensityRestrictedGlobalMap_map :
    presheafDensityRestrictedGlobalMap F x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap (SSet.const z) G
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion F x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion_target F x) =
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison p x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsLiftedMap F := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_pointed]
    simp only [presheafDensityRestrictedGlobalMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsLiftedMap,
      Category.assoc, pullback.lift_fst]
  · change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G = _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_projection, ← Category.assoc,
      presheafDensityRestrictedGlobalMap_projection, presheafDensityRestrictedGlobalBase]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsLiftedMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection,
      Category.assoc, pullback.lift_snd]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
