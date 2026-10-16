module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftFillers

/-! # Actual simplicial evaluation and parameterized action of the presented word category

The source and value universes remain independent. Universe lifts are used
only to put tensor factors in a common auxiliary universe; no model is used.
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordPresentationAction
open WordPresentationRealization WordPresentationNaturality
variable {C : Type u} [Category.{w} C] {T : SSet.{v}}
  (F : C ⥤ ParameterCategory.Object T) (K : C → SSet.{v})
  (s : ∀ X, K X ⟶ (F.obj X).value) (p : ∀ X, (F.obj X).value ⟶ K X)
  (hs : ∀ X, s X ≫ p X = 𝟙 (K X))
  (H : ∀ X, SSet.Homotopy (𝟙 (F.obj X).value) (p X ≫ s X))
  (hP : ∀ X, (H X).h ≫ p X = fst (F.obj X).value WordSegment.interval ≫ p X)
  (hS : ∀ X, s X ▷ WordSegment.interval ≫ (H X).h = fst (K X) WordSegment.interval ≫ s X)

def action (X Y : C) : UniverseLift.obj.{max u w v} (K X) ⊗
    (UniverseLift.obj.{max u w v} T ⊗ WordPresentationDiagram.smallHom.{u, w, v} C X Y) ⟶
      UniverseLift.obj.{max u w v} (K Y) where
  app n := ↾fun x => ULift.up ((R F K s p hs H hP hS n x.2.1.down).functor.map x.2.2 x.1.down)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up
      (small_naturality F K s p hs H hP hS θ x.2.1.down X Y x.2.2 x.1.down).symm

def family {U : SSet.{max u w v}} (X Y : C)
    (t : U ⟶ UniverseLift.obj.{max u w v} T)
    (f : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C X Y) :
    UniverseLift.obj.{max u w v} (K X) ⊗ U ⟶ UniverseLift.obj.{max u w v} (K Y) :=
  UniverseLift.obj (K X) ◁ lift t f ≫ action F K s p hs H hP hS X Y

lemma family_substitute {U V : SSet.{max u w v}} (X Y : C)
    (t : U ⟶ UniverseLift.obj.{max u w v} T)
    (f : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C X Y) (j : V ⟶ U) :
    family F K s p hs H hP hS X Y (j ≫ t) (j ≫ f) =
      ParameterComposition.substitute j (family F K s p hs H hP hS X Y t f) := by
  ext n x
  rfl

lemma family_identity {U : SSet.{max u w v}} (X : C)
    (t : U ⟶ UniverseLift.obj.{max u w v} T) :
    family F K s p hs H hP hS X X t
      (SSet.stdSimplex.isTerminalObj₀.from U ≫ WordPresentationDiagram.identity C X) =
      fst (UniverseLift.obj (K X)) U := by
  ext n x
  change ULift.up ((R F K s p hs H hP hS n (t.app n x.2).down).functor.map
    (𝟙 ((RetractWords.quotient C (WordSegment.degree.{v} n)).obj (.small X))) x.1.down) = x.1
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma family_comp {U : SSet.{max u w v}} (X Y Z : C)
    (t : U ⟶ UniverseLift.obj.{max u w v} T)
    (f : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C X Y)
    (g : U ⟶ WordPresentationDiagram.smallHom.{u, w, v} C Y Z) :
    ParameterComposition.comp (family F K s p hs H hP hS X Y t f)
        (family F K s p hs H hP hS Y Z t g) =
      family F K s p hs H hP hS X Z t (lift f g ≫ WordPresentationDiagram.composition C X Y Z) := by
  ext n x
  change _ = ULift.up ((R F K s p hs H hP hS n (t.app n x.2).down).functor.map
    (f.app n x.2 ≫ g.app n x.2) x.1.down)
  rw [CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.SimplicialModel.WordPresentationAction
