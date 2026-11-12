module
public import SerrePositivity.KST.Fibration.WeakStringCofiberMiddle
public import SerrePositivity.KST.SConstruction.RelativeMultiRealizationAdditivity

/-! # 元の相対 K-1 から得る核の作用と W 辺の終点評価

E(B,B,ker q) の同じ二評価を逆にし、元の中間評価への作用射を構成する。
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

/-- 元の相対 K-1 の二評価と中間評価から構成する、核の全正有限反復での作用。 -/
def weakRelativeMultiAction {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.obj
      ((multiRealizationFunctor (r + 1)).obj
        (closedStableModel (ClosedStablePredicate.top (sInputModel B))) ⊗
        (multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q))) ⟶
      AnodyneHomotopy.anodyneQ.obj
        ((multiRealizationFunctor (r + 1)).obj
          (closedStableModel (ClosedStablePredicate.top (sInputModel B)))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeMultiRealizationAdditivityMap (r + 1)
        (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q))) :=
    relativeMultiRealizationAdditivityMap_localized_isIso r _ _
  exact inv (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap (r + 1)
    (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q))) ≫
      AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map (weakRelativeMiddle q))

/-- 元の相対図式の中間評価は、同じ二評価の射対と核の作用の合成である。 -/
lemma weakRelativeMultiAction_factor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap (r + 1)
      (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)) ≫
        weakRelativeMultiAction q r =
        AnodyneHomotopy.anodyneQ.map
          ((multiRealizationFunctor (r + 1)).map (weakRelativeMiddle q)) := by
  unfold weakRelativeMultiAction
  simp only [IsIso.hom_inv_id_assoc]

/-- 任意の元の相対完全関手の中間評価を、同じ始点と核値 cofiber の作用で回収する。 -/
lemma weakRelativeMultiAction_of_relativeFunctor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (r : ℕ) {X : StableModel.{u}}
    (f : X ⟶ weakCofiberModel q) :
    AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
      (f ≫ weakRelativeMiddle q)) =
        AnodyneHomotopy.anodyneQ.map (lift
          ((multiRealizationFunctor (r + 1)).map
            (f ≫ relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
              (kernelClosedPredicate q)))
          ((multiRealizationFunctor (r + 1)).map
            (f ≫ relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
              (kernelClosedPredicate q)))) ≫
              weakRelativeMultiAction q r := by
  have hp : (multiRealizationFunctor (r + 1)).map f ≫
      relativeMultiRealizationAdditivityMap (r + 1)
        (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q) = lift
      ((multiRealizationFunctor (r + 1)).map
        (f ≫ relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
              (kernelClosedPredicate q)))
      ((multiRealizationFunctor (r + 1)).map
        (f ≫ relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
              (kernelClosedPredicate q))) := by
    simp only [relativeMultiRealizationAdditivityMap, comp_lift, Functor.map_comp]
  rw [← hp]
  simp only [Functor.map_comp]
  rw [Category.assoc, weakRelativeMultiAction_factor]

end SerrePositivity.KST.Fibration
