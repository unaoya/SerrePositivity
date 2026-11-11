module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ElementsDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ElementsYonedaSliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.ElementsYonedaSliceEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.YonedaSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

/-!
概要：元の小さい元の圏から Yoneda slice への比較を、反転と宇宙持ち上げを揃えて使う。
方針：元の実比較を反転し、ULift と反転の厳密な同型を前後に入れる。
規約：元の底を厳密に保持する。使われ方：同じ有限全余錐の切断制限の移送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 同じ Yoneda slice を反転し、底の反転と ULift の順を厳密に揃えた射影。 -/
def oppositeYonedaSliceProjection :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSlice F).op ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C.op :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSliceProjection F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso C).inv

instance oppositeYonedaSliceProjection_leftFibration : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (oppositeYonedaSliceProjection F) where
  mem := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSliceProjection F)))
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso C).inv)

/-- 元の大域比較自身を反転し、同じ小さい反転全空間からの写像として読む。 -/
def oppositeElementsYonedaSliceComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F).op ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSlice F).op :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F)).hom ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafElementsYonedaSliceComparison F)

/-- 同じ反転比較は、元の反転した小さい射影の持ち上げを厳密に保つ。 -/
lemma oppositeElementsYonedaSliceComparison_projection :
    oppositeElementsYonedaSliceComparison F ≫ oppositeYonedaSliceProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F)) := by
  have h := congrArg SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafElementsYonedaSliceComparison_projection F)
  rw [SSet.opFunctor.map_comp] at h
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F)).hom ≫
        (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafElementsYonedaSliceComparison F) ≫
          SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSliceProjection F)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso C).inv := by
      simp only [oppositeElementsYonedaSliceComparison, oppositeYonedaSliceProjection, Category.assoc]
    _ = _ := by
      rw [h]
      change ((SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso C).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso C).inv = _
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 元の実比較の反転も、前合成の同値条件を満たす。 -/
lemma oppositeElementsYonedaSliceComparison_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (oppositeElementsYonedaSliceComparison F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F))).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isPrecompositionEquivalence_op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafElementsYonedaSliceComparison_isQCatEquivalence F).isPrecompositionEquivalence)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
