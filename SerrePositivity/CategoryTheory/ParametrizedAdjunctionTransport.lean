module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Whiskering

/-! # Restriction and transport of parametrized adjunctions

Natural comparisons transport the parameter compatibility together with the
ordinary adjunctions. No new adjunction structure is introduced.
-/

@[expose] public section
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
namespace SerrePositivity.ParametrizedAdjunctionTransport
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {F F' : A ⥤ B ⥤ C} {G G' : Aᵒᵖ ⥤ C ⥤ B}

/-- Restrict the parameter along a functor. -/
def restrict (adj : F ⊣₂ G) (P : D ⥤ A) : (P ⋙ F) ⊣₂ (P.op ⋙ G) := by
  refine ParametrizedAdjunction.mk' (fun X ↦ adj.adj (P.obj X)) ?_
  intro X Y f Z W g
  exact adj.homEquiv_naturality_one (P.map f) g

/-- Compose an ordinary adjunction in the second input, retaining parameter naturality. -/
def composeSecond (adj : F ⊣₂ G) {L : D ⥤ B} {R : B ⥤ D} (h : L ⊣ R) :
    (F ⋙ (CategoryTheory.Functor.whiskeringLeft D B C).obj L) ⊣₂
      (G ⋙ (CategoryTheory.Functor.whiskeringRight C B D).obj R) := by
  refine ParametrizedAdjunction.mk' (fun X ↦ h.comp (adj.adj X)) ?_
  intro X Y f Z W g
  simp only [Adjunction.comp_homEquiv]
  change h.homEquiv _ _ (adj.homEquiv ((F.map f).app (L.obj Z) ≫ g)) =
    h.homEquiv _ _ (adj.homEquiv g) ≫ R.map ((G.map f.op).app W)
  rw [adj.homEquiv_naturality_one]
  exact h.homEquiv_naturality_right _ _

/-- Transport the left bifunctor through a natural isomorphism. -/
def left (adj : F ⊣₂ G) (e : F ≅ F') : F' ⊣₂ G := by
  refine ParametrizedAdjunction.mk' (fun X ↦ (adj.adj X).ofNatIsoLeft (e.app X)) ?_
  intro X Y f Z W g
  simp only [Adjunction.homEquiv_ofNatIsoLeft_apply]
  have hn := congrArg (fun t ↦ t.app Z) (e.hom.naturality f)
  change (F.map f).app Z ≫ (e.hom.app Y).app Z =
    (e.hom.app X).app Z ≫ (F'.map f).app Z at hn
  change (adj.adj X).homEquiv Z W
    ((e.hom.app X).app Z ≫ (F'.map f).app Z ≫ g) =
      (adj.adj Y).homEquiv Z W ((e.hom.app Y).app Z ≫ g) ≫ (G.map f.op).app W
  rw [← Category.assoc, ← hn, Category.assoc]
  exact adj.homEquiv_naturality_one f ((e.hom.app Y).app Z ≫ g)

/-- Transport the right bifunctor through a natural isomorphism. -/
def right (adj : F ⊣₂ G) (e : G ≅ G') : F ⊣₂ G' := by
  refine ParametrizedAdjunction.mk' (fun X ↦ (adj.adj X).ofNatIsoRight (e.app (op X))) ?_
  intro X Y f Z W g
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply]
  change (adj.adj X).homEquiv Z W ((F.map f).app Z ≫ g) ≫
    (e.hom.app (op X)).app W =
      ((adj.adj Y).homEquiv Z W g ≫ (e.hom.app (op Y)).app W) ≫ (G'.map f.op).app W
  have h := adj.homEquiv_naturality_one f g
  change (adj.adj X).homEquiv Z W ((F.map f).app Z ≫ g) =
    (adj.adj Y).homEquiv Z W g ≫ (G.map f.op).app W at h
  rw [h, Category.assoc]
  have hn := congrArg (fun t ↦ t.app W) (e.hom.naturality f.op)
  change (G.map f.op).app W ≫ (e.hom.app (op X)).app W =
    (e.hom.app (op Y)).app W ≫ (G'.map f.op).app W at hn
  rw [hn, Category.assoc]

end SerrePositivity.ParametrizedAdjunctionTransport
