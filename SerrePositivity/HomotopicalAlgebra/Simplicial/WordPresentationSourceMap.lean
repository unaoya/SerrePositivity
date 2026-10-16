module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationDiagram

/-! # Actual maps of word Hom simplicial sets induced by arbitrary source functors -/

@[expose] public section
universe u v u' v' w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.WordPresentationSourceMap
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

lemma commute {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    RetractWords.map F (MonoidWithZeroHom.id (WordSegment.degree.{w} n)) ⋙
        RetractWords.map (𝟭 D) (WordSegment.degreeMap θ) =
      RetractWords.map (𝟭 C) (WordSegment.degreeMap θ) ⋙
        RetractWords.map F (MonoidWithZeroHom.id (WordSegment.degree m)) := by
  rw [← RetractWords.map_comp, ← RetractWords.map_comp]
  simp only [Functor.comp_id, Functor.id_comp, MonoidWithZeroHom.comp_id,
    MonoidWithZeroHom.id_comp]

-- Both Hom objects must be lifted to a common universe when the sources differ.
def mapHom (X Y : C) : SSet.uliftFunctor.{max u' v', max u v w}.obj
    (WordPresentationDiagram.smallHom.{u, v, w} C X Y) ⟶
    SSet.uliftFunctor.{max u v, max u' v' w}.obj
      (WordPresentationDiagram.smallHom.{u', v', w} D (F.obj X) (F.obj Y)) where
  app n := ↾fun f => ULift.up
    ((RetractWords.map F (MonoidWithZeroHom.id (WordSegment.degree.{w} n))).map f.down)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congr($(commute.{u, v, u', v', w} F θ).map f.down)
    exact congrArg ULift.up h.symm

section CommonUniverse
variable {E : Type u} [Category.{v} E] (G : C ⥤ E)

def mapHomSame (X Y : C) : WordPresentationDiagram.smallHom.{u, v, w} C X Y ⟶
    WordPresentationDiagram.smallHom.{u, v, w} E (G.obj X) (G.obj Y) where
  app n := ↾fun f => (RetractWords.map G (MonoidWithZeroHom.id (WordSegment.degree.{w} n))).map f
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congr($(commute.{u, v, u, v, w} G θ).map f)
    exact h.symm

lemma mapHomSame_identity (X Y : C) : mapHomSame.{u, v, w} (𝟭 C) X Y =
    𝟙 (WordPresentationDiagram.smallHom.{u, v, w} C X Y) := by
  ext n f
  have h := congr($(RetractWords.map_id (C := C) (M := WordSegment.degree.{w} n)).map f)
  exact h

open CategoryTheory.MonoidalCategory

lemma mapHomSame_composition (X Y Z : C) :
    WordPresentationDiagram.composition.{u, v, w} C X Y Z ≫ mapHomSame G X Z =
      mapHomSame G X Y ▷ WordPresentationDiagram.smallHom C Y Z ≫
        WordPresentationDiagram.smallHom E (G.obj X) (G.obj Y) ◁ mapHomSame G Y Z ≫
          WordPresentationDiagram.composition E (G.obj X) (G.obj Y) (G.obj Z) := by
  ext n f
  exact (RetractWords.map G (MonoidWithZeroHom.id (WordSegment.degree.{w} n))).map_comp f.1 f.2

lemma mapHomSame_unit (X : C) :
    WordPresentationDiagram.identity.{u, v, w} C X ≫ mapHomSame G X X =
      WordPresentationDiagram.identity E (G.obj X) := by
  ext n x
  exact (RetractWords.map G (MonoidWithZeroHom.id (WordSegment.degree.{w} n))).map_id
    ((RetractWords.quotient C _).obj (.small X))

variable {E' : Type u} [Category.{v} E'] (G' : E ⥤ E')
lemma mapHomSame_comp (X Y : C) : mapHomSame.{u, v, w} (G ⋙ G') X Y =
    mapHomSame G X Y ≫ mapHomSame G' (G.obj X) (G.obj Y) := by
  ext n f
  have hf := RetractWords.map_comp G G'
    (MonoidWithZeroHom.id (WordSegment.degree.{w} n)) (MonoidWithZeroHom.id _)
  simp only [MonoidWithZeroHom.comp_id] at hf
  have h := congr($(hf).map f)
  exact h

end CommonUniverse

end SerrePositivity.SimplicialModel.WordPresentationSourceMap
