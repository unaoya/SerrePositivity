module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafDensitySourceRestriction

/-!
概要：元の共同 Hom の全変換を始点固定に制限し、同じ密度変換の評価と照合する。
方針：二変数 curry の評価公式で全円柱の厳密な等式を示す。
規約：元の大域変換を用い、各点で別の変換を選択しない。
使われ方：元の unstraightening 写像空間比較の底変換自然性への入力。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F

/-- 評価した元の密度変換の全円柱は、元の共同 Hom の全変換の始点固定。 -/
lemma presheafDensityDiagramHomotopy_evaluation :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityDiagramHomotopy F).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x =
      (((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion F x)) ▷
        (Δ[1] : SSet.{u + 1})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityJointHomotopy F).h := by
  change curry ((α_ ((SSet.uliftFunctor.{u + 1, u}).obj C.op)
      ((SSet.uliftFunctor.{u + 1, u}).obj E) (Δ[1] : SSet.{u + 1})).inv ≫
        (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} C.op E).inv ▷
          (Δ[1] : SSet.{u + 1})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityJointHomotopy F).h)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 始点固定の同じ共同 Hom の変換を、元の評価図式の両端で読む。 -/
def presheafDensityRestrictedHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationDiagram F x)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationVertex F x)) where
  h := (((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion F x)) ▷
    (Δ[1] : SSet.{u + 1})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityJointHomotopy F).h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityJointHomotopy F).h₀]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion_source F x
  h₁ := by
    rw [SSet.ι₁_comp_assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityJointHomotopy F).h₁]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensitySourceInclusion_target F x
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
