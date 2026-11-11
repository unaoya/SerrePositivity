module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafDensityEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：元の共同 Hom の二変数の底を始点固定に制限し、同じ密度評価図式を厳密に回収する。
方針：元の curry の評価公式と、宇宙持ち上げと積の交換の座標を使う。
規約：元の全図式を使い、値ごとの同型で代用しない。
使われ方：大域密度変換の unstraightening の底変換自然性への入力。

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
local notation "p" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F

/-- 始点を元の対象に固定し、元の小さい元の圏を第二変数として保つ底の包含。 -/
def presheafDensitySourceInclusion : E ⟶ C.op ⊗ E :=
  lift (SSet.const (SSet.opObjEquiv.symm x)) (𝟙 E)

/-- 同じ共同 Hom の始点固定は、元の Yoneda 図式の同じ評価そのもの。 -/
lemma presheafDensitySourceInclusion_source :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsHomDiagram p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationDiagram F x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationDiagram, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensity_source_curry F]
  change _ = curry
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} C.op E).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsHomDiagram p) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

omit [Quasicategory C] in
/-- 同じ標的図式の始点固定は、元の F の指定値に定値な図式そのもの。 -/
lemma presheafDensitySourceInclusion_target :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsTargetDiagram F =
        SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationVertex F x) := by
  have hk : (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (fst C.op E) =
      SSet.const (ULift.up (SSet.opObjEquiv.symm x)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafTwistedElementsTargetDiagram, ← Category.assoc, hk, SSet.const_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationVertex_value]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
