module

public import Mathlib.CategoryTheory.Presentable.SolutionSetCondition
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Small solution families of commutative squares

An accessible full subcategory of the arrow category, with accessible inclusion,
provides small solution families for each source arrow. No model structure or
smallness of the entire morphism property is assumed.
-/

@[expose] public section
universe w t v u
noncomputable section
open CategoryTheory
namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- Regard a morphism property as an object property of the existing arrow category. -/
abbrev arrowProperty : ObjectProperty (Arrow C) := fun f ↦ W f.hom

/-- The full inclusion of arrows satisfying the candidate weak equivalences. -/
abbrev arrowInclusion : (arrowProperty W).FullSubcategory ⥤ Arrow C :=
  (arrowProperty W).ι

variable [IsAccessibleCategory.{w} (Arrow C)]
  [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
  [(arrowInclusion W).IsAccessible.{w}]

/-- Mathlib's solution-set condition, derived from accessibility. -/
lemma solutionSetCondition : SolutionSetCondition.{w} (arrowInclusion W) :=
  SolutionSetCondition.of_isCardinalAccessible (arrowInclusion W)

/-- The small indexing type supplied by the solution-set condition for an arrow. -/
def solutionIndex (i : Arrow C) : Type w :=
  Classical.choose (solutionSetCondition W i)

/-- A chosen target arrow, still carrying its membership in W. -/
def solutionArrow (i : Arrow C) (j : solutionIndex W i) :
    (arrowProperty W).FullSubcategory :=
  (Classical.choose (Classical.choose_spec (solutionSetCondition W i))) j

/-- The chosen square from the source arrow to a solution arrow. -/
def solutionSquare (i : Arrow C) (j : solutionIndex W i) :
    i ⟶ (solutionArrow W i j).obj :=
  (Classical.choose (Classical.choose_spec
    (Classical.choose_spec (solutionSetCondition W i)))) j

/-- Every square into W factors as an actual composite of arrow-category maps. -/
lemma solutionSquare_factor (i f : Arrow C) (hf : W f.hom) (sq : i ⟶ f) :
    ∃ (j : solutionIndex W i) (g : (solutionArrow W i j).obj ⟶ f),
      solutionSquare W i j ≫ g = sq := by
  obtain ⟨j, g, h⟩ := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (solutionSetCondition W i))))
      ⟨f, hf⟩ sq
  exact ⟨j, (arrowInclusion W).map g, h⟩

/-- The factorization also gives the two component equations of the square. -/
lemma solutionSquare_factor_components (i f : Arrow C) (hf : W f.hom) (sq : i ⟶ f) :
    ∃ (j : solutionIndex W i) (g : (solutionArrow W i j).obj ⟶ f),
      (solutionSquare W i j).left ≫ g.left = sq.left ∧
      (solutionSquare W i j).right ≫ g.right = sq.right := by
  obtain ⟨j, g, h⟩ := solutionSquare_factor W i f hf sq
  exact ⟨j, g, congrArg Arrow.Hom.left h, congrArg Arrow.Hom.right h⟩

end SerrePositivity.Smith
