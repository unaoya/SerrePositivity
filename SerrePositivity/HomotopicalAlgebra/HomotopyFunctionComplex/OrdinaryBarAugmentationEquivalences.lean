module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftPadding

/-! # Both original simplex augmentations in the ordinary bar evaluation square are inverted

The explicit source lift and the original small-output padding are
retained. No equivalence of the evaluation or of the row map is assumed.
-/

@[expose] public section
universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

def sourceIso : SSet.uliftFunctor.{max u v, max u v}.obj
    (nerve (OrdinaryBarTotalCone.Index R)) ≅
      SimplexNerve.functor.obj (OrdinaryBarEvaluation.bar R) :=
  NatIso.ofComponents (fun _ =>
    { toFun := fun x => x.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl : _ ≃ _ }.toIso) (by intro _ _ _; rfl)

lemma large_eq : OrdinaryBarNerveBridge.simplexAugmentation R =
    (sourceIso R).hom ≫ SimplexNerve.augmentation.app (OrdinaryBarEvaluation.bar R) := rfl

lemma large_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarNerveBridge.simplexAugmentation R)) := by
  have := SimplexNerve.augmentation_localized_isIso (OrdinaryBarEvaluation.bar R)
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (SimplexNerve.augmentation.app (OrdinaryBarEvaluation.bar R))) := this
  rw [large_eq, CategoryTheory.Functor.map_comp]
  infer_instance

lemma small_eq : OrdinaryBarEvaluatedEndpoint.smallAugmentation R =
    SSet.uliftFunctor.{max u v, v}.map
      (SimplexNerve.augmentation.app (OrdinaryBarFirstAction.output R)) ≫
        (UniverseLift.paddingIso.{v, u}.app (OrdinaryBarFirstAction.output R)).inv := rfl

lemma small_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarEvaluatedEndpoint.smallAugmentation R)) := by
  have := UniverseLift.anodyneQ_map_isIso_of_small.{max u v, v}
    (SimplexNerve.augmentation.app (OrdinaryBarFirstAction.output R))
    (SimplexNerve.augmentation_localized_isIso _)
  have : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{max u v, v}.map
      (SimplexNerve.augmentation.app (OrdinaryBarFirstAction.output R)))) := this
  rw [small_eq, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences
