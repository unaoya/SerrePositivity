module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices

/-! # All native composition triangles form a small relative extension space

The earlier selected triangle is a point of this space. Whole parameter
boundaries of triangles extend while the two original comparison edges
stay fixed throughout the extension.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z)

abbrev compositionChoices : SSet.{v} := ComparisonTriangleChoices.obj
  (nativeRestrictionComparison hcof hfib P j
    (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
  (compositionComparison hcof hfib P j f g c d)

lemma compositionChoices_boundary_rlp : SSet.modelCategoryQuillen.I.rlp
    (terminal.from (compositionChoices hcof hfib P j f g c d e)) :=
  ComparisonTriangleChoices.boundary_rlp _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z))

lemma compositionChoices_kan : SSet.modelCategoryQuillen.J.rlp
    (terminal.from (compositionChoices hcof hfib P j f g c d e)) :=
  ComparisonTriangleChoices.kan _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z))

def selectedCompositionPoint : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶
    compositionChoices hcof hfib P j f g c d e :=
  ComparisonTriangleChoices.ofData _ _ (compositionTriangle hcof hfib P j f g c d e)

def compositionChoiceFamily {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    T ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ⟶
      (ihom (small hcof hfib X)).obj (small hcof hfib Z) :=
  uncurry (ComparisonTriangleChoices.family _ _ q)

lemma compositionChoiceFamily_zero {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    T ◁ (SSet.stdSimplex.δ (0 : Fin 3) ▷ L) ≫
      compositionChoiceFamily hcof hfib P j f g c d e q =
    T ◁ fst (SSet.stdSimplex.obj (SimplexCategory.mk 1)) L ≫
      (compositionComparison hcof hfib P j f g c d).h := by
  rw [compositionChoiceFamily, ← uncurry_natural_left, ComparisonTriangleChoices.family_zero,
    uncurry_natural_left, uncurry_curry]

lemma compositionChoiceFamily_one {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    T ◁ (SSet.stdSimplex.δ (1 : Fin 3) ▷ L) ≫
      compositionChoiceFamily hcof hfib P j f g c d e q =
    T ◁ fst (SSet.stdSimplex.obj (SimplexCategory.mk 1)) L ≫
      (nativeRestrictionComparison hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e).h := by
  rw [compositionChoiceFamily, ← uncurry_natural_left, ComparisonTriangleChoices.family_one,
    uncurry_natural_left, uncurry_curry]

lemma compositionChoiceFamily_selected :
    compositionChoiceFamily hcof hfib P j f g c d e
      (selectedCompositionPoint hcof hfib P j f g c d e) =
    T ◁ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
      (ρ_ (SSet.stdSimplex.obj (SimplexCategory.mk 2))).hom) ≫
        compositionTriangleFamily hcof hfib P j f g c d e := by
  rw [compositionChoiceFamily, selectedCompositionPoint, ComparisonTriangleChoices.ofData_family,
    ← Category.assoc, uncurry_natural_left]

lemma compositionChoices_relative_extension {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    (q : U ⟶ compositionChoices hcof hfib P j f g c d e) :
    ∃ r : V ⟶ compositionChoices hcof hfib P j f g c d e, i ≫ r = q ∧
      T ◁ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ i) ≫
        compositionChoiceFamily hcof hfib P j f g c d e r =
          compositionChoiceFamily hcof hfib P j f g c d e q := by
  obtain ⟨r, hr, hfamily⟩ := ComparisonTriangleChoices.relative_extension _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z)) i q
  refine ⟨r, hr, ?_⟩
  rw [compositionChoiceFamily, ← uncurry_natural_left, hfamily]
  rfl

abbrev compositionTriangleData := KanComparisonTriangle.Data
  (nativeRestrictionComparison hcof hfib P j
    (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
  (compositionComparison hcof hfib P j f g c d)

abbrev comparisonOfCompositionTriangles
    (a b : compositionTriangleData hcof hfib P j f g c d e) :=
  ComparisonTriangleChoices.fixedBoundaryComparison _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z)) a b

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
