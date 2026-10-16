module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift

/-! # Small boundary fillers across simplicial universes

This extends the existing universe-lift API. Finite boundary fillers in
the smaller universe supply fillers after lifting; no larger model
structure is needed.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.UniverseLift

abbrev obj (P : SSet.{v}) : SSet.{max w v} := SSet.uliftFunctor.{w, v}.obj P
abbrev map {P Q : SSet.{v}} (f : P ⟶ Q) : obj.{w} P ⟶ obj.{w} Q :=
  SSet.uliftFunctor.{w, v}.map f

def lower {P Q : SSet.{v}} (f : obj.{w} P ⟶ obj.{w} Q) : P ⟶ Q where
  app n := ↾fun x => (f.app n ⟨x⟩).down
  naturality {_ _} θ := by
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact congrArg ULift.down (congrArg (fun h => h (ULift.up x)) (f.naturality θ))

lemma map_lower {P Q : SSet.{v}} (f : obj.{w} P ⟶ obj.{w} Q) : map (lower f) = f := rfl
lemma lower_map {P Q : SSet.{v}} (f : P ⟶ Q) : lower (map.{w} f) = f := rfl

@[reassoc]
lemma map_comp {P Q R : SSet.{v}} (f : P ⟶ Q) (g : Q ⟶ R) :
    map.{w} (f ≫ g) = map f ≫ map g := rfl

abbrev stdIso (d : ℕ) : obj.{w} (SSet.stdSimplex.{v}.obj (SimplexCategory.mk d)) ≅
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk d) := simplexIso (SimplexCategory.mk d)

@[reassoc]
lemma boundary_square (d : ℕ) :
    map.{w} (SSet.boundary.{v} d).ι ≫ (stdIso.{w, v} d).hom =
      (boundaryIso.{w, v} d).hom ≫ (SSet.boundary.{max w v} d).ι := rfl

/-- Existence of fillers for all finite boundaries, before choosing a model structure. -/
abbrev BoundaryFillers (P : SSet.{v}) : Prop := ∀ (d : ℕ)
  (b : (SSet.boundary.{v} d).toSSet ⟶ P),
  ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk d) ⟶ P, (SSet.boundary.{v} d).ι ≫ e = b

lemma boundaryFillers {P : SSet.{v}} (hp : BoundaryFillers P) : BoundaryFillers (obj.{w} P) := by
  intro d b
  obtain ⟨e, he⟩ := hp d (lower ((boundaryIso.{w, v} d).hom ≫ b))
  refine ⟨(stdIso.{w, v} d).inv ≫ map e, ?_⟩
  apply (cancel_epi (boundaryIso.{w, v} d).hom).mp
  calc
    _ = (map (SSet.boundary.{v} d).ι ≫ (stdIso.{w, v} d).hom) ≫
        (stdIso.{w, v} d).inv ≫ map e := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ (stdIso.{w, v} d).inv ≫ map e) (boundary_square.{w, v} d).symm
    _ = map ((SSet.boundary.{v} d).ι ≫ e) := by
      rw [Category.assoc, Iso.hom_inv_id_assoc, map_comp]
    _ = _ := by rw [he, map_lower]

end SerrePositivity.SimplicialModel.UniverseLift
