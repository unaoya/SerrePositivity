module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionOfFunctor
public import SerrePositivity.CategoryTheory.RelativeArrow

/-! # The category of Reedy attaching diagrams at one fixed object

A morphism is a natural transformation below the current degree together
with its compatible map on the attached object. Relative boundary arrows
are then functors on its arrow category, including when the lower diagrams
change by a natural isomorphism.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) (C : Type u') [Category.{v'} C]

structure BoundaryDiagram where
  lower : Lower r (r.deg j) ⥤ C
  extension : BoundaryExtension r j lower

namespace BoundaryDiagram
variable {r j C}

structure Hom (D E : BoundaryDiagram r j C) where
  lower : D.lower ⟶ E.lower
  upper : BoundaryExtension.Map D.extension E.extension lower

@[ext]
lemma Hom.ext {D E : BoundaryDiagram r j C} {f g : Hom D E}
    (hl : f.lower = g.lower) (hu : f.upper.hom = g.upper.hom) : f = g := by
  rcases f with ⟨l, ⟨u, hi, ho⟩⟩
  rcases g with ⟨l', ⟨u', hi', ho'⟩⟩
  cases hl
  cases hu
  rfl

abbrev Hom.id (D : BoundaryDiagram r j C) : Hom D D where
  lower := 𝟙 D.lower
  upper :=
    { hom := 𝟙 D.extension.obj
      incoming f hf := by rw [Category.comp_id]; exact (Category.id_comp _).symm
      outgoing {x} f hf := by
        change D.extension.outgoing f hf ≫ 𝟙 (D.lower.obj x) =
          𝟙 D.extension.obj ≫ D.extension.outgoing f hf
        rw [Category.comp_id, Category.id_comp] }

abbrev Hom.comp {D E F : BoundaryDiagram r j C} (m : Hom D E) (n : Hom E F) : Hom D F where
  lower := m.lower ≫ n.lower
  upper :=
    { hom := m.upper.hom ≫ n.upper.hom
      incoming f hf := by
        rw [← Category.assoc, m.upper.incoming, Category.assoc, n.upper.incoming,
          ← Category.assoc]
        rfl
      outgoing f hf := by
        change D.extension.outgoing f hf ≫ (m.lower.app _ ≫ n.lower.app _) = _
        rw [← Category.assoc, m.upper.outgoing, Category.assoc, n.upper.outgoing,
          ← Category.assoc] }

instance : Category (BoundaryDiagram r j C) where
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

abbrev ofExtension {H : Lower r (r.deg j) ⥤ C} (d : BoundaryExtension r j H) :
    BoundaryDiagram r j C := ⟨H, d⟩

abbrev homOfMap {H K : Lower r (r.deg j) ⥤ C}
    {d : BoundaryExtension r j H} {e : BoundaryExtension r j K}
    {τ : H ⟶ K} (m : d.Map e τ) : ofExtension d ⟶ ofExtension e := ⟨τ, m⟩

variable (r j C)

abbrev lowerFunctor : BoundaryDiagram r j C ⥤ (Lower r (r.deg j) ⥤ C) where
  obj D := D.lower
  map f := f.lower

abbrev objectFunctor : BoundaryDiagram r j C ⥤ C where
  obj D := D.extension.obj
  map f := f.upper.hom

abbrev fromFunctor : (J ⥤ C) ⥤ BoundaryDiagram r j C where
  obj F := ofExtension (BoundaryExtension.ofFunctor r j F)
  map τ := homOfMap (BoundaryExtension.mapOfNatTrans r j τ)
  map_id F := by apply Hom.ext <;> rfl
  map_comp τ σ := by apply Hom.ext <;> rfl

section Latching
variable [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C]

abbrev latchingComparison : lowerFunctor r j C ⋙ lowerLatchingEvaluation r j ⟶
    objectFunctor r j C where
  app D := D.extension.latchingMap
  naturality _ _ f := f.upper.latching_naturality

abbrev relativeLatchingArrow : Arrow (BoundaryDiagram r j C) ⥤ Arrow C :=
  RelativeArrow.pushoutFunctor (latchingComparison r j C)

@[simp]
lemma relativeLatchingArrow_fromFunctor {F G : J ⥤ C} (τ : F ⟶ G) :
    ((relativeLatchingArrow r j C).obj (Arrow.mk ((fromFunctor r j C).map τ))).hom =
      SerrePositivity.Reedy.relativeLatchingMap r j τ := rfl

end Latching

section Matching
variable [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C]

abbrev matchingComparison : objectFunctor r j C ⟶
    lowerFunctor r j C ⋙ lowerMatchingEvaluation r j where
  app D := D.extension.matchingMap
  naturality _ _ f := f.upper.matching_naturality

abbrev relativeMatchingArrow : Arrow (BoundaryDiagram r j C) ⥤ Arrow C :=
  RelativeArrow.pullbackFunctor (matchingComparison r j C)

@[simp]
lemma relativeMatchingArrow_fromFunctor {F G : J ⥤ C} (τ : F ⟶ G) :
    ((relativeMatchingArrow r j C).obj (Arrow.mk ((fromFunctor r j C).map τ))).hom =
      SerrePositivity.Reedy.relativeMatchingMap r j τ := rfl

end Matching
end BoundaryDiagram
end SerrePositivity.Reedy
