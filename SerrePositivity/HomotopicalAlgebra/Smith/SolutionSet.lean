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

/-- Collect the chosen target arrows for a family of source arrows. -/
def solutionTargets {ι : Type t} (a : ι → Arrow C) : MorphismProperty C :=
  MorphismProperty.ofHoms (fun x : Σ k, solutionIndex W (a k) ↦
    (solutionArrow W (a x.1) x.2).obj.hom)

instance solutionTargets_isSmall {ι : Type t} [Small.{w} ι] (a : ι → Arrow C) :
    (solutionTargets W a).IsSmall.{w} := by
  unfold solutionTargets
  infer_instance

lemma solutionTargets_le {ι : Type t} (a : ι → Arrow C) : solutionTargets W a ≤ W := by
  rintro _ _ _ ⟨x⟩
  exact (solutionArrow W (a x.1) x.2).property

/-- The small union still solves every square from each member of the source family. -/
lemma solutionTargets_factor {ι : Type t} (a : ι → Arrow C) (k : ι)
    (f : Arrow C) (hf : W f.hom) (sq : a k ⟶ f) :
    ∃ g : Arrow C, solutionTargets W a g.hom ∧
      ∃ (p : a k ⟶ g) (q : g ⟶ f), p ≫ q = sq := by
  obtain ⟨j, q, h⟩ := solutionSquare_factor W (a k) f hf sq
  refine ⟨(solutionArrow W (a k) j).obj, ?_, solutionSquare W (a k) j, q, h⟩
  unfold solutionTargets
  exact MorphismProperty.ofHoms.mk
    (f := fun x : Σ k, solutionIndex W (a k) ↦ (solutionArrow W (a x.1) x.2).obj.hom)
    ⟨k, j⟩

/-- The same collection for a morphism property, using its actual arrow subtype. -/
abbrev solutionTargetsForClass (I : MorphismProperty C) : MorphismProperty C :=
  solutionTargets W (fun i : I.toSet ↦ i.val)

instance solutionTargetsForClass_isSmall (I : MorphismProperty C) [I.IsSmall.{w}] :
    (solutionTargetsForClass W I).IsSmall.{w} := by
  exact solutionTargets_isSmall W (fun i : I.toSet ↦ i.val)

lemma solutionTargetsForClass_le (I : MorphismProperty C) :
    solutionTargetsForClass W I ≤ W := solutionTargets_le W _

/-- No smallness of W is required to solve all squares out of a small source class. -/
lemma solutionTargetsForClass_factor (I : MorphismProperty C) (i f : Arrow C)
    (hi : I i.hom) (hf : W f.hom) (sq : i ⟶ f) :
    ∃ g : Arrow C, solutionTargetsForClass W I g.hom ∧
      ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq :=
  solutionTargets_factor W (fun i : I.toSet ↦ i.val) ⟨i, hi⟩ f hf sq

end SerrePositivity.Smith
