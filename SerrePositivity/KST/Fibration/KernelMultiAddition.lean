module
public import SerrePositivity.KST.Fibration.KernelRelativeMiddle
public import SerrePositivity.KST.SConstruction.RelativeMultiRealizationAdditivity

/-! # K-1 の相対加法性から得る核の全正有限反復の加法射

元の E(ker q,B,ker q) の二評価の局所化同型を逆にし、中間評価を通す。
任意の相対完全関手の中間評価は、元の両端の射対を通して厳密に因子分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- K-1 の元の二評価と中間評価から構成する、核の正有限反復実現の加法射。 -/
def kernelMultiAddition {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.obj
      ((multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q)) ⊗
        (multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q))) ⟶
      AnodyneHomotopy.anodyneQ.obj
        ((multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeMultiRealizationAdditivityMap (r + 1)
        (kernelClosedPredicate q) (kernelClosedPredicate q))) :=
    relativeMultiRealizationAdditivityMap_localized_isIso r _ _
  exact inv (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap (r + 1)
    (kernelClosedPredicate q) (kernelClosedPredicate q))) ≫
      AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map (kernelRelativeMiddle q))

/-- 元の相対図式の中間評価は、K-1 の二評価の射対と加法射の合成である。 -/
lemma kernelMultiAddition_factor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap (r + 1)
      (kernelClosedPredicate q) (kernelClosedPredicate q)) ≫ kernelMultiAddition q r =
        AnodyneHomotopy.anodyneQ.map
          ((multiRealizationFunctor (r + 1)).map (kernelRelativeMiddle q)) := by
  unfold kernelMultiAddition
  simp only [IsIso.hom_inv_id_assoc]

/-- 任意の元の相対完全関手の中間評価に対する、全正有限反復の加法性。 -/
lemma kernelMultiAddition_of_relativeFunctor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (r : ℕ) {X : StableModel.{u}}
    (f : X ⟶ relativeCofiberStableModel (kernelClosedPredicate q) (kernelClosedPredicate q)) :
    AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
      (f ≫ kernelRelativeMiddle q)) =
        AnodyneHomotopy.anodyneQ.map (lift
          ((multiRealizationFunctor (r + 1)).map
            (f ≫ relativeCofiberSubobject (kernelClosedPredicate q) (kernelClosedPredicate q)))
          ((multiRealizationFunctor (r + 1)).map
            (f ≫ relativeCofiberQuotient (kernelClosedPredicate q) (kernelClosedPredicate q)))) ≫
              kernelMultiAddition q r := by
  have hp : (multiRealizationFunctor (r + 1)).map f ≫
      relativeMultiRealizationAdditivityMap (r + 1)
        (kernelClosedPredicate q) (kernelClosedPredicate q) = lift
      ((multiRealizationFunctor (r + 1)).map
        (f ≫ relativeCofiberSubobject (kernelClosedPredicate q) (kernelClosedPredicate q)))
      ((multiRealizationFunctor (r + 1)).map
        (f ≫ relativeCofiberQuotient (kernelClosedPredicate q) (kernelClosedPredicate q))) := by
    simp only [relativeMultiRealizationAdditivityMap, comp_lift, Functor.map_comp]
  rw [← hp]
  simp only [Functor.map_comp]
  rw [Category.assoc, kernelMultiAddition_factor]

end SerrePositivity.KST.Fibration
