module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationFixedTarget

/-!
概要：元の大域 pointed 評価を同じ始点固定の全族で制限し、同じ定値標的へ持ち上げる。
方針：元の pointed 成分と終点成分を引き戻しに入れ、全体への射を両成分で照合する。
規約：元の評価・指定値・同じ全族を保持する。
使われ方：密度の評価変換の像を元の始点固定評価と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "z" => presheafDensityEvaluationVertex F x

/-- 同じ始点固定の全族の共同射影は、指定された全体側の底そのもの。 -/
lemma presheafDensityRestrictedGlobalBase :
    presheafDensityEvaluationSourceBase F x ≫
      (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (twistedElementsProjection p) := by
  simpa only [presheafDensityEvaluationGlobalBase, twistedElementsReconstruction_projection]
    using presheafDensityEvaluationSourceBase_global F x

/-- 元の pointed 評価の同じ制限は、同じ定値標的を被覆する。 -/
lemma presheafDensityRestrictedGlobalMap_over :
    ((SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      presheafTwistedElementsEvaluation F) ≫ pointedSpaceProjection =
    presheafDensityEvaluationSourceBase F x ≫ (SSet.const z) := by
  rw [Category.assoc, presheafTwistedElementsEvaluation_over, ← Category.assoc,
    ← presheafDensityRestrictedGlobalBase, Category.assoc,
    presheafDensitySourceInclusion_target]

/-- 元の大域評価の始点固定を、同じ評価の定値 unstraightening へ戻す。 -/
def presheafDensityRestrictedGlobalMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (twistedSourceElements p x) ⟶
      leftUnstraightening (SSet.const z :
        (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶ SpaceInfinity.{u}) :=
  pullback.lift
    ((SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      presheafTwistedElementsEvaluation F) (presheafDensityEvaluationSourceBase F x)
    (presheafDensityRestrictedGlobalMap_over F x)

/-- 同じ制限評価は、元の終点の全空間への射影を保つ。 -/
lemma presheafDensityRestrictedGlobalMap_projection :
    presheafDensityRestrictedGlobalMap F x ≫ leftUnstraighteningProjection (SSet.const z) =
      presheafDensityEvaluationSourceBase F x := pullback.lift_snd _ _ _

/-- 同じ制限評価を元の大域標的へ戻すと、元の大域評価の同じ制限。 -/
lemma presheafDensityRestrictedGlobalMap_map :
    presheafDensityRestrictedGlobalMap F x ≫ leftUnstraighteningMap (SSet.const z) G
      ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
      (presheafDensitySourceInclusion_target F x) =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      presheafTwistedElementsLiftedMap F := by
  apply pullback.hom_ext
  · rw [Category.assoc, leftUnstraighteningMap_pointed]
    simp only [presheafDensityRestrictedGlobalMap, presheafTwistedElementsLiftedMap,
      Category.assoc, pullback.lift_fst]
  · change _ ≫ leftUnstraighteningProjection G = _ ≫ leftUnstraighteningProjection G
    rw [Category.assoc, leftUnstraighteningMap_projection, ← Category.assoc,
      presheafDensityRestrictedGlobalMap_projection, presheafDensityRestrictedGlobalBase]
    simp only [presheafTwistedElementsLiftedMap, leftUnstraighteningProjection,
      Category.assoc, pullback.lift_snd]

end SerrePositivity.InfinityCategories.F2.Ind
