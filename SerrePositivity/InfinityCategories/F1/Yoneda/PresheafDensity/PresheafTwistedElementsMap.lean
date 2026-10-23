module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafTwistedElementsEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedElementsBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningLift

/-!
概要：大域 pointed 評価を、同じ二変数の底上の実際の unstraightening 間の射へ戻す。
方針：pointed-space の引き戻しの普遍性で大きい射を作り、小さい代表へ降ろす。
規約：元の F と元の全 twisted arrow 族を保持し、底の可換性は厳密。
使われ方：共同 Hom の unstraightening からの相対射への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
local notation "E" => smallRightUnstraightening F
local notation "p" => smallRightUnstraighteningProjection F

/-- 同じ二変数の底の上で、元の F を始点変数だけで評価する図式。 -/
def presheafTwistedElementsTargetDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ E) ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (fst C.op E) ≫ F

/-- 大域 pointed 評価は、同じ二変数の底の図式を厳密に被覆する。 -/
lemma presheafTwistedElementsEvaluation_over :
    presheafTwistedElementsEvaluation F ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 1, u}).map (twistedElementsProjection p) ≫
        presheafTwistedElementsTargetDiagram F := by
  rw [presheafTwistedElementsTargetDiagram, ← Category.assoc, ← Functor.map_comp,
    twistedElementsProjection, lift_fst, presheafTwistedElementsEvaluation_projection]

/-- 同じ大域評価を、元の unstraightening の引き戻しへ戻した射。 -/
def presheafTwistedElementsLiftedMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (presheafTwistedElements F) ⟶
      leftUnstraightening (presheafTwistedElementsTargetDiagram F) :=
  pullback.lift (presheafTwistedElementsEvaluation F)
    ((SSet.uliftFunctor.{u + 1, u}).map (twistedElementsProjection p))
    (presheafTwistedElementsEvaluation_over F)

/-- 元の小さい全空間の同じ大域評価に対応する、実際の相対射。 -/
def presheafTwistedElementsMap : presheafTwistedElements F ⟶
    smallLeftUnstraightening (presheafTwistedElementsTargetDiagram F) :=
  smallLeftUnstraighteningLift _ (presheafTwistedElementsLiftedMap F)

/-- 同じ小さい相対射は元の二変数の共同射影を厳密に保つ。 -/
lemma presheafTwistedElementsMap_projection :
    presheafTwistedElementsMap F ≫ smallLeftUnstraighteningProjection
      (presheafTwistedElementsTargetDiagram F) = twistedElementsProjection p :=
  smallLeftUnstraighteningLift_projection _ _ _ (pullback.lift_snd _ _ _)

end SerrePositivity.InfinityCategories.F2.Ind
