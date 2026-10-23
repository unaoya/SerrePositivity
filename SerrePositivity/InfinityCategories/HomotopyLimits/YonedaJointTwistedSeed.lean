module

public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaEvaluationJointFibrations
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseTwistedArrowProjection
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftClassification

/-!
概要：元の全 twisted arrow から、共同 Yoneda Hom と共同評価の両全空間への射を構成。
方針：元の Yoneda を twisted arrow に適用し、同じ元の全復元射を評価全空間へ送る。
規約：元の全 twisted arrow の全単体と同じ両変数の底を保持する。
使われ方：大域 Yoneda 評価比較射が保持すべき、一つの全恒等点・全射の族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
local instance {X : SSet.{u}} [Quasicategory X] : Quasicategory (X.op ⊗ X) :=
  quasicategory_of_innerFibration (CartesianMonoidalCategory.fst X.op X)
variable (C : SSet.{u}) [Quasicategory C]

/-- 元の両端の底を、元の Yoneda と全前層の共同底へ送る元の写像。 -/
def yonedaJointYonedaBaseMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ C) ⟶ YonedaEvaluationJointBase C :=
  (uliftTensorIso C.op C).hom ≫ (𝟙 _ ⊗ₘ yonedaInfinityMap C)

/-- 元の共同評価への同じ写像の制限は、元の共同 Hom の分類図式そのもの。 -/
lemma yonedaJointYonedaBaseMap_evaluation :
    yonedaJointYonedaBaseMap C ≫ yonedaEvaluationJointNative C =
      twistedArrowHomInfinity C := by
  change (uliftTensorIso C.op C).hom ≫
    ((((SSet.uliftFunctor.{u + 1, u}).obj C.op) ◁ yonedaInfinityMap C) ≫
      (ihom.ev _).app SpaceInfinity.{u}) = _
  rw [← uncurry_eq, yonedaInfinityMap_uncurry]
  exact (uliftTensorIso C.op C).hom_inv_id_assoc _

/-- 元の全 twisted arrow を、同じ両変数の共同底へ送る元の射。 -/
def yonedaJointTwistedBase :
    (SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow C) ⟶ YonedaEvaluationJointBase C :=
  (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowProjection C) ≫ yonedaJointYonedaBaseMap C

/-- 元の全 twisted arrow の Yoneda 像を、元の共同 Hom 全空間へ厳密に持ち上げる。 -/
def yonedaHomJointTwistedSeed :
    (SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow C) ⟶ yonedaHomJointTotal C :=
  pullback.lift
    ((uliftTwistedArrowIso C).hom ≫ edgewiseSubdivisionMap (yonedaInfinityMap C))
    (yonedaJointTwistedBase C) (by
      rw [Category.assoc, twistedArrowProjection_naturality, ← Category.assoc,
        uliftTwistedArrowIso_projection]
      apply SSet.hom_ext
      intro n
      rfl)

/-- 元の全 twisted arrow の Hom 側の像は、同じ元の共同底を厳密に保つ。 -/
lemma yonedaHomJointTwistedSeed_projection :
    yonedaHomJointTwistedSeed C ≫ yonedaHomJointProjection C = yonedaJointTwistedBase C :=
  pullback.lift_snd _ _ _

/-- 同じ元の全復元射を使い、元の全 twisted arrow を共同評価全空間へ送る。 -/
def yonedaEvaluationJointTwistedSeed :
    (SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow C) ⟶ yonedaEvaluationJointTotal C :=
  leftClassificationUniverseComparison (twistedArrowProjection C) ≫
    leftUnstraighteningMap (twistedArrowHomInfinity C) (yonedaEvaluationJointNative C)
      (yonedaJointYonedaBaseMap C) (yonedaJointYonedaBaseMap_evaluation C)

/-- 元の全 twisted arrow の評価側の像も、同じ元の共同底を厳密に保つ。 -/
lemma yonedaEvaluationJointTwistedSeed_projection :
    yonedaEvaluationJointTwistedSeed C ≫ yonedaEvaluationJointProjection C =
      yonedaJointTwistedBase C := by
  change (leftClassificationUniverseComparison (twistedArrowProjection C) ≫
    leftUnstraighteningMap (twistedArrowHomInfinity C) (yonedaEvaluationJointNative C)
      (yonedaJointYonedaBaseMap C) (yonedaJointYonedaBaseMap_evaluation C)) ≫
    leftUnstraighteningProjection (yonedaEvaluationJointNative C) = _
  rw [Category.assoc, leftUnstraighteningMap_projection, ← Category.assoc]
  change (leftClassificationUniverseComparison (twistedArrowProjection C) ≫
    leftUnstraighteningProjection (leftStraighteningInfinityDiagram (twistedArrowProjection C))) ≫
    yonedaJointYonedaBaseMap C = _
  rw [leftClassificationUniverseComparison_projection]
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
