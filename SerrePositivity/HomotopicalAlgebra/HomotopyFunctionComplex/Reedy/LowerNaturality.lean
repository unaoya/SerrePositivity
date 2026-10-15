module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Degree

/-! # Naturality within a degree restriction

The actual Reedy factorization of a map whose endpoints are below a remains
below a, so naturality on the two restricted Reedy classes suffices.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (a : α) {C : Type u'} [Category.{v'} C]
  {F G : J ⥤ C}

lemma identities_on_lower {x y : Lower r a} (f : x ⟶ y)
    (hf : MorphismProperty.identities J f.hom) :
    MorphismProperty.identities (Lower r a) f := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases f with ⟨f⟩
  cases hf
  exact MorphismProperty.ofHoms.mk _

lemma naturality_on_lower_identities (app : ∀ x : Lower r a, F.obj x.obj ⟶ G.obj x.obj)
    {x y : Lower r a} (f : x ⟶ y) (hf : MorphismProperty.identities J f.hom) :
    F.map f.hom ≫ app y = app x ≫ G.map f.hom := by
  have h := identities_on_lower r a f hf
  cases h
  simp

include r in
lemma naturality_on_lower (app : ∀ x : Lower r a, F.obj x.obj ⟶ G.obj x.obj)
    (hinverse : ∀ {x y : Lower r a} (f : x ⟶ y), inverse f.hom →
      F.map f.hom ≫ app y = app x ≫ G.map f.hom)
    (hdirect : ∀ {x y : Lower r a} (f : x ⟶ y), direct f.hom →
      F.map f.hom ≫ app y = app x ≫ G.map f.hom)
    {x y : Lower r a} (f : x ⟶ y) : F.map f.hom ≫ app y = app x ≫ G.map f.hom := by
  obtain ⟨Z, p, i, hp, hi, hpi, _⟩ := r.exists_fac f.hom
  let z : Lower r a := ⟨Z, lt_of_le_of_lt (r.le₁ p hp) x.property⟩
  have h₁ := hinverse (ObjectProperty.homMk p : x ⟶ z) hp
  have h₂ := hdirect (ObjectProperty.homMk i : z ⟶ y) hi
  change F.map p ≫ app z = app x ≫ G.map p at h₁
  change F.map i ≫ app y = app z ≫ G.map i at h₂
  rw [← hpi, F.map_comp, G.map_comp, Category.assoc, h₂, ← Category.assoc, h₁,
    Category.assoc]

def natTransOnLowerOfReedy (app : ∀ x : Lower r a, F.obj x.obj ⟶ G.obj x.obj)
    (hinverse : ∀ {x y : Lower r a} (f : x ⟶ y), inverse f.hom →
      F.map f.hom ≫ app y = app x ≫ G.map f.hom)
    (hdirect : ∀ {x y : Lower r a} (f : x ⟶ y), direct f.hom →
      F.map f.hom ≫ app y = app x ≫ G.map f.hom) :
    lowerInclusion r a ⋙ F ⟶ lowerInclusion r a ⋙ G where
  app := app
  naturality _ _ f := naturality_on_lower r a app hinverse hdirect f

end SerrePositivity.Reedy
