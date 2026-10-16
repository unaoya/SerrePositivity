module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Algebra.GroupWithZero.Hom

/-! # A category presented by source arrows, contraction words, and split retracts

The quotient is formed from the stated relations and their congruence closure,
not from an evaluation kernel. Objects and parameter universes are independent.
-/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]

inductive Vertex (C : Type u) (M : Type w)
  | ambient : C → Vertex C M
  | small : C → Vertex C M

inductive Edge : Vertex C M → Vertex C M → Type (max u v w)
  | source {X Y : C} (f : X ⟶ Y) : Edge (.ambient X) (.ambient Y)
  | word (X : C) (t : M) : Edge (.ambient X) (.ambient X)
  | section_ (X : C) : Edge (.small X) (.ambient X)
  | projection (X : C) : Edge (.ambient X) (.small X)

instance : Quiver (Vertex C M) := ⟨Edge C M⟩

abbrev Raw := Paths (Vertex C M)

abbrev source {X Y : C} (f : X ⟶ Y) :
    @Quiver.Path (Vertex C M) (instQuiverVertex C M) (.ambient X) (.ambient Y) :=
  (Paths.of (Vertex C M)).map (.source f)
abbrev word (X : C) (t : M) :
    @Quiver.Path (Vertex C M) (instQuiverVertex C M) (.ambient X) (.ambient X) :=
  (Paths.of (Vertex C M)).map (.word X t)
abbrev section_ (X : C) :
    @Quiver.Path (Vertex C M) (instQuiverVertex C M) (.small X) (.ambient X) :=
  (Paths.of (Vertex C M)).map (.section_ X)
abbrev projection (X : C) :
    @Quiver.Path (Vertex C M) (instQuiverVertex C M) (.ambient X) (.small X) :=
  (Paths.of (Vertex C M)).map (.projection X)

inductive Rel : HomRel (Raw C M)
  | source_id (X : C) : Rel (source C M (𝟙 X)) (𝟙 _)
  | source_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
      Rel (source C M f ≫ source C M g) (source C M (f ≫ g))
  | word_one (X : C) : Rel (word C M X 1) (𝟙 _)
  | word_mul (X : C) (t z : M) : Rel (word C M X t ≫ word C M X z) (word C M X (t * z))
  | split (X : C) : Rel (section_ C M X ≫ projection C M X) (𝟙 _)
  | word_zero (X : C) : Rel (word C M X 0) (projection C M X ≫ section_ C M X)
  | section_word (X : C) (t : M) : Rel (section_ C M X ≫ word C M X t) (section_ C M X)
  | word_projection (X : C) (t : M) : Rel (word C M X t ≫ projection C M X) (projection C M X)

abbrev Obj := CategoryTheory.Quotient (Rel C M)
abbrev quotient : Raw C M ⥤ Obj C M := CategoryTheory.Quotient.functor (Rel C M)

abbrev Small := InducedCategory (Obj C M) (fun X : C => (quotient C M).obj (.small X))

def sourceFunctor : C ⥤ Obj C M where
  obj X := (quotient C M).obj (.ambient X)
  map f := (quotient C M).map (source C M f)
  map_id X := by
    simpa using CategoryTheory.Quotient.sound (Rel C M) (Rel.source_id X)
  map_comp f g := by
    simpa using (CategoryTheory.Quotient.sound (Rel C M) (Rel.source_comp f g)).symm

def augmentationEdges : Vertex C M ⥤q C where
  obj
    | .ambient X => X
    | .small X => X
  map
    | .source f => f
    | .word _ _ => 𝟙 _
    | .section_ _ => 𝟙 _
    | .projection _ => 𝟙 _

abbrev rawAugmentation : Raw C M ⥤ C := Paths.lift (augmentationEdges C M)

lemma augmentation_rel {X Y : Raw C M} {f g : X ⟶ Y} (h : Rel C M f g) :
    (rawAugmentation C M).map f = (rawAugmentation C M).map g := by
  cases h <;>
    simp only [rawAugmentation, Functor.map_comp, Functor.map_id, source, word, section_,
      projection, Paths.of_map, Paths.lift_toPath] <;>
    dsimp [augmentationEdges, Paths.lift] <;> simp

def augmentation : Obj C M ⥤ C :=
  CategoryTheory.Quotient.lift (Rel C M) (rawAugmentation C M)
    (fun _ _ _ _ h => augmentation_rel C M h)

def smallAugmentation : Small C M ⥤ C :=
  inducedFunctor _ ⋙ augmentation C M

lemma source_augmentation : sourceFunctor C M ⋙ augmentation C M = 𝟭 C := by
  refine CategoryTheory.Functor.ext
    (F := sourceFunctor C M ⋙ augmentation C M) (G := 𝟭 C) (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (rawAugmentation C M).map (source C M f) = f
  exact Paths.lift_toPath (augmentationEdges C M) (Edge.source f)

end SerrePositivity.RetractWords
