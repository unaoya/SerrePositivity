module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpace

/-! # Source change for actual spaces of augmented lifts

An actual map of augmented cosimplicial diagrams induces a map of pullback
fibers. Both the augmentation square and the base map square are retained.
No model structure or functorial choice of resolutions is used here.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.LiftSpacePrecomposition
variable {C : Type u} [Category.{v} C]
  (A A' : SimplexCategory ⥤ C) {X Y : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X)
  (a' : A' ⟶ (Functor.const SimplexCategory).obj Y)
  (k : X ⟶ Y) (φ : A ⟶ A')
  (hφ : φ ≫ a' = a ≫ (Functor.const SimplexCategory).map k)

include hφ in
lemma point {B : C} (fX : X ⟶ B) (fY : Y ⟶ B) (hf : k ≫ fY = fX) :
    LiftSpace.point A' a' fY ≫ (cosimplicialHomMap φ).app B = LiftSpace.point A a fX := by
  ext n x
  change φ.app n.unop ≫ (a'.app n.unop ≫ fY) = a.app n.unop ≫ fX
  have h := congr_app hφ n.unop
  change φ.app n.unop ≫ a'.app n.unop = a.app n.unop ≫ k at h
  rw [← Category.assoc, h, Category.assoc, hf]

def map {E B : C} (p : E ⟶ B) (fX : X ⟶ B) (fY : Y ⟶ B) (hf : k ≫ fY = fX) :
    LiftSpace.obj A' a' p fY ⟶ LiftSpace.obj A a p fX :=
  pullback.lift (LiftSpace.inclusion A' a' p fY ≫ (cosimplicialHomMap φ).app E)
    (LiftSpace.projection A' a' p fY) (by
      rw [Category.assoc, ← (cosimplicialHomMap φ).naturality p, ← Category.assoc,
        LiftSpace.over, Category.assoc, point A A' a a' k φ hφ fX fY hf])

@[reassoc (attr := simp)]
lemma map_inclusion {E B : C} (p : E ⟶ B) (fX : X ⟶ B) (fY : Y ⟶ B) (hf : k ≫ fY = fX) :
    map A A' a a' k φ hφ p fX fY hf ≫ LiftSpace.inclusion A a p fX =
      LiftSpace.inclusion A' a' p fY ≫ (cosimplicialHomMap φ).app E :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_projection {E B : C} (p : E ⟶ B) (fX : X ⟶ B) (fY : Y ⟶ B) (hf : k ≫ fY = fX) :
    map A A' a a' k φ hφ p fX fY hf ≫ LiftSpace.projection A a p fX =
      LiftSpace.projection A' a' p fY := pullback.lift_snd _ _ _

lemma ofLift {E B : C} (p : E ⟶ B) (fX : X ⟶ B) (fY : Y ⟶ B) (hf : k ≫ fY = fX)
    (e : Y ⟶ E) (he : e ≫ p = fY) :
    LiftSpace.ofLift A' a' p fY e he ≫ map A A' a a' k φ hφ p fX fY hf =
      LiftSpace.ofLift A a p fX (k ≫ e) (by rw [Category.assoc, he, hf]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, map_inclusion, ← Category.assoc, LiftSpace.ofLift_inclusion]
    exact (point A A' a a' k φ hφ (k ≫ e) e rfl).trans
      (LiftSpace.ofLift_inclusion A a p fX (k ≫ e) _).symm
  · rw [Category.assoc, map_projection, LiftSpace.ofLift_projection]
    exact (LiftSpace.ofLift_projection A a p fX (k ≫ e) _).symm

end SerrePositivity.HomotopyFunctionComplex.LiftSpacePrecomposition
