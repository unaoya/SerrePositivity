module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceMaps

/-! # Relative choice spaces in a strict diagram

Fixed boundary and extension data are natural transformations. Their actual
pullback fibers, transport maps, and selected points form strict functors.
No model structure is needed for this construction.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.RelativeChoiceFunctor
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  {A K : SSet.{v}} (i : A ⟶ K) (b : (Functor.const D).obj A ⟶ F)

lemma boundary_naturality {X Y : D} (f : X ⟶ Y) : b.app X ≫ F.map f = b.app Y :=
  (b.naturality f).symm.trans (Category.id_comp _)

def functor : D ⥤ SSet.{v} where
  obj X := RelativeChoiceSpace.obj i (b.app X)
  map f := RelativeChoiceSpace.postMap i _ _ (F.map f) (boundary_naturality F b f)
  map_id X := by
    simp only [F.map_id]
    exact RelativeChoiceSpace.postMap_identity _ _
  map_comp f g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, RelativeChoiceSpace.postMap_inclusion,
        RelativeChoiceSpace.postMap_inclusion_assoc, F.map_comp]
      rw [CategoryTheory.Functor.map_comp]
    · simp only [Category.assoc, RelativeChoiceSpace.postMap_projection]

def projection : functor F i b ⟶ (Functor.const D).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) where
  app X := RelativeChoiceSpace.projection i (b.app X)
  naturality {X Y} f := by
    change (functor F i b).map f ≫ RelativeChoiceSpace.projection i (b.app Y) =
      RelativeChoiceSpace.projection i (b.app X) ≫ (𝟙 _)
    exact (RelativeChoiceSpace.postMap_projection i (b.app X) (b.app Y) (F.map f)
      (boundary_naturality F b f)).trans (Category.comp_id _).symm

variable (a : (Functor.const D).obj K ⟶ F) (ha : ∀ X, i ≫ a.app X = b.app X)

/-- An actual natural family of extensions supplies a strictly natural point. -/
def point : (Functor.const D).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶
    functor F i b where
  app X := RelativeChoiceSpace.ofExtension i (b.app X) (a.app X) (ha X)
  naturality {X Y} f := by
    change (𝟙 _) ≫ _ = _
    rw [Category.id_comp]
    change RelativeChoiceSpace.ofExtension i (b.app Y) (a.app Y) (ha Y) =
      RelativeChoiceSpace.ofExtension i (b.app X) (a.app X) (ha X) ≫
        RelativeChoiceSpace.postMap i (b.app X) (b.app Y) (F.map f) (boundary_naturality F b f)
    rw [RelativeChoiceSpace.postMap_ofExtension]
    exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _
      ((a.naturality f).symm.trans (Category.id_comp _)).symm

lemma point_projection : point F i b a ha ≫ projection F i b = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  exact RelativeChoiceSpace.ofExtension_projection _ _ _ (ha X)

end SerrePositivity.SimplicialModel.RelativeChoiceFunctor
