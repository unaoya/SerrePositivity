module
public import SerrePositivity.DifferentialGraded.Module.RingDGComparison
public import SerrePositivity.DifferentialGraded.Functor.HomIso

/-! # 一対象Aとのdg比較が誘導する実際のH⁰同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

instance ringConstantDGHomotopyFull : (ringConstantDG A).onHomotopy.Full :=
  (ringConstantDG A).onHomotopy_full_of_homIso (fun P Q => by
    change IsIso (ringConstantHomIso A P Q).inv
    infer_instance)

instance ringConstantDGHomotopyFaithful : (ringConstantDG A).onHomotopy.Faithful :=
  (ringConstantDG A).onHomotopy_faithful_of_homIso (fun P Q => by
    change IsIso (ringConstantHomIso A P Q).inv
    infer_instance)

instance ringConstantDGHomotopyIsEquivalence : (ringConstantDG A).onHomotopy.IsEquivalence where

/-- 実際の定数dg関手のH⁰による同値。 -/
def ringConstantHomotopyEquivalence : HomotopyCategory A (Complex A) ≌
    HomotopyCategory A (RightModule A PUnit.{1}) :=
  (ringConstantDG A).onHomotopy.asEquivalence

instance ringEvaluationDGHomotopyFull :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.Full :=
  (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy_full_of_homIso
    (fun _ _ => by dsimp [moduleEvaluationDG]; infer_instance)

instance ringEvaluationDGHomotopyFaithful :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.Faithful :=
  (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy_faithful_of_homIso
    (fun _ _ => by dsimp [moduleEvaluationDG]; infer_instance)

instance ringEvaluationDGHomotopyIsEquivalence :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.IsEquivalence where

/-- 実際の評価dg関手のH⁰による同値。 -/
def ringEvaluationHomotopyEquivalence : HomotopyCategory A (RightModule A PUnit.{1}) ≌
    HomotopyCategory A (Complex A) :=
  (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.asEquivalence

end SerrePositivity.DifferentialGraded
