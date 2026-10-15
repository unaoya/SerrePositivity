module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeExtension

/-! # The category of one-step Reedy factorization problems

Objects retain an actual attaching-diagram arrow and a factorization of
its lower restriction. Morphisms consist of a square of attaching diagrams
and a middle natural transformation commuting with both lower factors.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) (C : Type u') [Category.{v'} C]

structure FactorizationProblem where
  source : Arrow (BoundaryDiagram r j C)
  factor : MorphismProperty.MapFactorizationData ⊤ ⊤ source.hom.lower

namespace FactorizationProblem
variable {r j C}

structure Hom (a b : FactorizationProblem r j C) where
  boundary : a.source ⟶ b.source
  middle : a.factor.Z ⟶ b.factor.Z
  left : boundary.left.lower ≫ b.factor.i = a.factor.i ≫ middle
  right : middle ≫ b.factor.p = a.factor.p ≫ boundary.right.lower

@[ext]
lemma Hom.ext {a b : FactorizationProblem r j C} {f g : Hom a b}
    (hb : f.boundary = g.boundary) (hm : f.middle = g.middle) : f = g := by
  cases f
  cases g
  cases hb
  cases hm
  rfl

abbrev Hom.id (a : FactorizationProblem r j C) : Hom a a where
  boundary := 𝟙 a.source
  middle := 𝟙 a.factor.Z
  left := (Category.id_comp _).trans (Category.comp_id _).symm
  right := (Category.id_comp _).trans (Category.comp_id _).symm

abbrev Hom.comp {a b c : FactorizationProblem r j C} (f : Hom a b) (g : Hom b c) : Hom a c where
  boundary := f.boundary ≫ g.boundary
  middle := f.middle ≫ g.middle
  left := by
    change (f.boundary.left.lower ≫ g.boundary.left.lower) ≫ c.factor.i = _
    rw [Category.assoc, g.left, ← Category.assoc, f.left, Category.assoc]
  right := by
    change (f.middle ≫ g.middle) ≫ c.factor.p =
      a.factor.p ≫ (f.boundary.right.lower ≫ g.boundary.right.lower)
    rw [Category.assoc, g.right, ← Category.assoc, f.right, Category.assoc]

instance : Category (FactorizationProblem r j C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    · exact Category.id_comp _
    · exact Category.id_comp _
  comp_id f := by
    apply Hom.ext
    · exact Category.comp_id _
    · exact Category.comp_id _
  assoc f g h := by
    apply Hom.ext
    · exact Category.assoc _ _ _
    · exact Category.assoc _ _ _

variable (r j C)

abbrev boundaryFunctor : FactorizationProblem r j C ⥤ Arrow (BoundaryDiagram r j C) where
  obj a := a.source
  map f := f.boundary

abbrev middleFunctor : FactorizationProblem r j C ⥤ (Lower r (r.deg j) ⥤ C) where
  obj a := a.factor.Z
  map f := f.middle

abbrev sourceFunctor : FactorizationProblem r j C ⥤ BoundaryDiagram r j C :=
  boundaryFunctor r j C ⋙ Arrow.leftFunc

abbrev targetFunctor : FactorizationProblem r j C ⥤ BoundaryDiagram r j C :=
  boundaryFunctor r j C ⋙ Arrow.rightFunc

end FactorizationProblem
end SerrePositivity.Reedy
