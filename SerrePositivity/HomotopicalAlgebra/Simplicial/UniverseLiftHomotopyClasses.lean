module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-! # Reflection of actual homotopies and comparison of their classes across universes -/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.UniverseLift

def lowerHomotopy {X K : SSet.{v}} {f g : X ⟶ K}
    (H : SSet.Homotopy (map.{w} f) (map.{w} g)) : SSet.Homotopy f g where
  h := lowerSimplexTensor H.h
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.down (congrArg (fun k => k.app n ⟨x⟩) H.h₀)
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.down (congrArg (fun k => k.app n ⟨x⟩) H.h₁)
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

def homotopyClassEquiv (X K : SSet.{v}) :
    HomotopyClasses.obj X K ≃ HomotopyClasses.obj (obj.{w} X) (obj.{w} K) where
  toFun := Quot.map map (fun _ _ ⟨H⟩ => ⟨homotopy H⟩)
  invFun := Quot.map lower (fun f g ⟨H⟩ => ⟨lowerHomotopy (f := lower f) (g := lower g) H⟩)
  left_inv x := Quot.inductionOn x (fun _ => rfl)
  right_inv x := Quot.inductionOn x (fun _ => rfl)

@[simp] lemma homotopyClassEquiv_mk {X K : SSet.{v}} (f : X ⟶ K) :
    homotopyClassEquiv.{w} X K (HomotopyClasses.mk f) = HomotopyClasses.mk (map f) := rfl

lemma homotopyClassEquiv_pre {A X K : SSet.{v}} (i : A ⟶ X) (x : HomotopyClasses.obj X K) :
    homotopyClassEquiv.{w} A K (HomotopyClasses.pre i x) =
      HomotopyClasses.pre (map i) (homotopyClassEquiv X K x) := by
  exact Quot.inductionOn x (fun _ => rfl)

lemma anodyne_map_iff {X Y : SSet.{v}} (i : X ⟶ Y) :
    SSet.anodyneExtensions (map.{w} i) ↔ SSet.anodyneExtensions i := by
  constructor
  · intro hi A B p hp
    have : HasLiftingProperty (map i) (map.{w} p) := hi _ ((horn_rightClass_iff p).mpr hp)
    exact (ModelGeneration.hasLiftingProperty_map_iff SSet.uliftFunctor i p).mp this
  · exact anodyne_map i

end SerrePositivity.SimplicialModel.UniverseLift
