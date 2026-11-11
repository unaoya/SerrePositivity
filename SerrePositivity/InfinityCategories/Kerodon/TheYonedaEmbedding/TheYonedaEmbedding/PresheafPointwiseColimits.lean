module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafCoherentColimitCones
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorColimitEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FunctorPointwiseColimitCriterion

/-!
概要：前層 ∞ 圏の小さい余極限と、元の評価による保存・検出。
方針：F2・N の各点余極限の存在と評価保存を元の前層評価へ移す。
規約：元の図式・余錐を保持し、底の quasicategory 性を要求しない。
使われ方：F1-4、HTT 5.1.2.2–5.1.2.4、Ind の基盤。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {B C : SSet.{u}}
  (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)

/-- 各点の小さい空間値余極限から、同じ前層図式の余極限全余錐が存在する。 -/
lemma presheafInfinity_exists_colimitCone :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ ∀ x : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) c) := by
  obtain ⟨c, hc, hcp⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoherentColimitCone_exists p
  exact ⟨c, hc, fun x ↦ hcp (ULift.up (SSet.opObjEquiv.symm x))⟩

/-- 任意の小さい形状の元の前層図式は余極限を持つ。 -/
lemma presheafInfinity_hasColimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  obtain ⟨c, hc, _⟩ := presheafInfinity_exists_colimitCone p
  exact ⟨c, hc⟩

/-- 同じ前層の任意の余極限全余錐は、元の各評価で余極限となる。 -/
lemma presheafInfinity_evaluation_isColimit (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (x : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) c) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isColimitCone_functor_evaluation_of_pointwise_exists c hc
    (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram p k))
    (ULift.up (SSet.opObjEquiv.symm x))

/-- 元の前層余錐が全評価で余極限なら、前層 ∞ 圏でも余極限。 -/
lemma presheafInfinity_isColimit_of_evaluation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise c
  intro k
  rcases k with ⟨k⟩
  obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective k
  exact hc x

/-- 小さい形状の前層余錐の余極限性は、元の全頂点評価によって保存・検出される。 -/
lemma presheafInfinity_isColimit_iff_evaluation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ ∀ x : C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x) c) :=
  ⟨presheafInfinity_evaluation_isColimit p c, presheafInfinity_isColimit_of_evaluation p c⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
