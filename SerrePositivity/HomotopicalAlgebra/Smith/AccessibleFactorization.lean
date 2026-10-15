module

public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Limits.Comma

/-! # Accessibility interfaces for specified functorial factorizations

Accessibility is a property of the specified data, not a consequence of
functoriality alone. The construction of accessible small-object data is a
separate part of A0. These lemmas transport that property to both arrow
factors and to restrictions along initial and terminal arrows.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Smith.AccessibleFactorization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Accessibility of an arrow-valued functor is detected on its endpoints. -/
lemma arrowFunctor_isCardinalAccessible (F : D ⥤ Arrow C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [(F ⋙ Arrow.leftFunc).IsCardinalAccessible κ]
    [(F ⋙ Arrow.rightFunc).IsCardinalAccessible κ] : F.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (F ⋙ Arrow.leftFunc) κ J
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (F ⋙ Arrow.rightFunc) κ J
    exact { preservesColimit := { preserves hc := ⟨
      Comma.fstSndJointlyReflectColimit
        (isColimitOfPreserves (F ⋙ Arrow.leftFunc) hc)
        (isColimitOfPreserves (F ⋙ Arrow.rightFunc) hc)⟩ } }

variable {L R : MorphismProperty C} (d : MorphismProperty.FunctorialFactorizationData L R)

def leftFactor : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (d.i.app f)
  map φ := Arrow.homMk φ.left (d.Z.map φ) (d.i.naturality φ)

def rightFactor : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (d.p.app f)
  map φ := Arrow.homMk (d.Z.map φ) φ.right (d.p.naturality φ)

section Accessibility
variable [HasColimitsOfSize.{w, w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [d.Z.IsCardinalAccessible κ]

lemma arrow_left_isCardinalAccessible :
    (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible κ :=
  inferInstanceAs ((Comma.fst (𝟭 C) (𝟭 C)).IsCardinalAccessible κ)

lemma arrow_right_isCardinalAccessible :
    (Arrow.rightFunc : Arrow C ⥤ C).IsCardinalAccessible κ :=
  inferInstanceAs ((Comma.snd (𝟭 C) (𝟭 C)).IsCardinalAccessible κ)

lemma leftFactor_isCardinalAccessible : (leftFactor d).IsCardinalAccessible κ := by
  have := arrow_left_isCardinalAccessible (C := C) κ
  have : (leftFactor d ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    inferInstanceAs ((Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible κ)
  have : (leftFactor d ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    inferInstanceAs (d.Z.IsCardinalAccessible κ)
  exact arrowFunctor_isCardinalAccessible _ κ

lemma rightFactor_isCardinalAccessible : (rightFactor d).IsCardinalAccessible κ := by
  have := arrow_right_isCardinalAccessible (C := C) κ
  have : (rightFactor d ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    inferInstanceAs (d.Z.IsCardinalAccessible κ)
  have : (rightFactor d ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    inferInstanceAs ((Arrow.rightFunc : Arrow C ⥤ C).IsCardinalAccessible κ)
  exact arrowFunctor_isCardinalAccessible _ κ

end Accessibility

section Replacement
variable [ModelCategory C]

def initialRestriction : C ⥤ C := ModelReplacement.initialArrows C ⋙ d.Z

def terminalRestriction : C ⥤ C := ModelReplacement.terminalArrows C ⋙ d.Z

def initialComparison : initialRestriction d ⟶ 𝟭 C where
  app X := d.p.app (Arrow.mk (initial.to X))
  naturality {_X _Y} f := d.p.naturality ((ModelReplacement.initialArrows C).map f)

def terminalComparison : 𝟭 C ⟶ terminalRestriction d where
  app X := d.i.app (Arrow.mk (terminal.from X))
  naturality {_X _Y} f := d.i.naturality ((ModelReplacement.terminalArrows C).map f)

lemma initialComparison_mem (X : C) : R ((initialComparison d).app X) := d.hp _

lemma terminalComparison_mem (X : C) : L ((terminalComparison d).app X) := d.hi _

lemma initialRestriction_isCofibrant
    (d : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C)) (X : C) :
    IsCofibrant ((initialRestriction d).obj X) :=
  (isCofibrant_iff_of_isInitial (d.i.app (Arrow.mk (initial.to X))) initialIsInitial).2
    ((cofibration_iff _).2 (d.hi _))

lemma terminalRestriction_isFibrant
    (d : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C)) (X : C) :
    IsFibrant ((terminalRestriction d).obj X) :=
  (isFibrant_iff_of_isTerminal (d.p.app (Arrow.mk (terminal.from X))) terminalIsTerminal).2
    ((fibration_iff _).2 (d.hp _))

lemma initialArrows_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (ModelReplacement.initialArrows C).IsCardinalAccessible κ := by
  have : (ModelReplacement.initialArrows C ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    inferInstanceAs (((Functor.const C).obj (⊥_ C)).IsCardinalAccessible κ)
  have : (ModelReplacement.initialArrows C ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    inferInstanceAs ((𝟭 C).IsCardinalAccessible κ)
  exact arrowFunctor_isCardinalAccessible _ κ

lemma terminalArrows_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (ModelReplacement.terminalArrows C).IsCardinalAccessible κ := by
  have : (ModelReplacement.terminalArrows C ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    inferInstanceAs ((𝟭 C).IsCardinalAccessible κ)
  have : (ModelReplacement.terminalArrows C ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    inferInstanceAs (((Functor.const C).obj (⊤_ C)).IsCardinalAccessible κ)
  exact arrowFunctor_isCardinalAccessible _ κ

lemma initialRestriction_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [d.Z.IsCardinalAccessible κ] : (initialRestriction d).IsCardinalAccessible κ := by
  have := initialArrows_isCardinalAccessible (C := C) κ
  exact inferInstanceAs ((ModelReplacement.initialArrows C ⋙ d.Z).IsCardinalAccessible κ)

lemma terminalRestriction_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [d.Z.IsCardinalAccessible κ] : (terminalRestriction d).IsCardinalAccessible κ := by
  have := terminalArrows_isCardinalAccessible (C := C) κ
  exact inferInstanceAs ((ModelReplacement.terminalArrows C ⋙ d.Z).IsCardinalAccessible κ)

end Replacement
end SerrePositivity.Smith.AccessibleFactorization
