module

public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.ElementsDiagram
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1B.Diagrams.OppositeLifting
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceComparison
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceEquivalence
public import SerrePositivity.InfinityCategories.F1.Ind.YonedaSlice
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeKanHomotopy

/-!
概要：元の小さい元の圏から Yoneda slice への比較を、反転と宇宙持ち上げを揃えて使う。
方針：元の実比較を反転し、ULift と反転の厳密な同型を前後に入れる。
規約：元の底を厳密に保持する。使われ方：同じ有限全余錐の切断制限の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 同じ Yoneda slice を反転し、底の反転と ULift の順を厳密に揃えた射影。 -/
def oppositeYonedaSliceProjection :
    (presheafYonedaSlice F).op ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C.op :=
  SSet.opFunctor.map (presheafYonedaSliceProjection F) ≫ (uliftOppositeIso C).inv

instance oppositeYonedaSliceProjection_leftFibration : LeftFibration (oppositeYonedaSliceProjection F) where
  mem := leftFibrations.comp_mem _ _
    (LeftFibration.mem (p := SSet.opFunctor.map (presheafYonedaSliceProjection F)))
    (MorphismProperty.of_isIso leftFibrations (uliftOppositeIso C).inv)

/-- 元の大域比較自身を反転し、同じ小さい反転全空間からの写像として読む。 -/
def oppositeElementsYonedaSliceComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F).op ⟶
      (presheafYonedaSlice F).op :=
  (uliftOppositeIso (smallRightUnstraightening F)).hom ≫
    SSet.opFunctor.map (presheafElementsYonedaSliceComparison F)

/-- 同じ反転比較は、元の反転した小さい射影の持ち上げを厳密に保つ。 -/
lemma oppositeElementsYonedaSliceComparison_projection :
    oppositeElementsYonedaSliceComparison F ≫ oppositeYonedaSliceProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (smallRightUnstraighteningProjection F)) := by
  have h := congrArg SSet.opFunctor.map (presheafElementsYonedaSliceComparison_projection F)
  rw [SSet.opFunctor.map_comp] at h
  calc
    _ = (uliftOppositeIso (smallRightUnstraightening F)).hom ≫
        (SSet.opFunctor.map (presheafElementsYonedaSliceComparison F) ≫
          SSet.opFunctor.map (presheafYonedaSliceProjection F)) ≫ (uliftOppositeIso C).inv := by
      simp only [oppositeElementsYonedaSliceComparison, oppositeYonedaSliceProjection, Category.assoc]
    _ = _ := by
      rw [h]
      change ((SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (smallRightUnstraighteningProjection F)) ≫
        (uliftOppositeIso C).hom) ≫ (uliftOppositeIso C).inv = _
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 元の実比較の反転も、前合成の同値条件を満たす。 -/
lemma oppositeElementsYonedaSliceComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (oppositeElementsYonedaSliceComparison F) :=
  (isPrecompositionEquivalence_of_iso (uliftOppositeIso (smallRightUnstraightening F))).comp
    (SerrePositivity.InfinityCategories.F1B.isPrecompositionEquivalence_op
      (presheafElementsYonedaSliceComparison_isQCatEquivalence F).isPrecompositionEquivalence)

end SerrePositivity.InfinityCategories.F2.Ind
