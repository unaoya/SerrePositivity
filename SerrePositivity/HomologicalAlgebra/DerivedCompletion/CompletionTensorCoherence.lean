module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTensorComparison
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Coherence of the canonical derived completion tensor comparison -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)
local notation "μ" => boundedAboveCompletionTensorComparison R a

/-- The completion tensor comparison respects the actual associator. -/
theorem boundedAboveCompletionTensorComparison_assoc (X Y Z : D) :
    (μ X Y ⊗ₘ 𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj Z)) ≫
      μ (X ⊗ Y) Z ≫ (boundedAboveDerivedCompletionFunctor R a).map (α_ X Y Z).hom =
    (α_ ((boundedAboveDerivedCompletionFunctor R a).obj X)
      ((boundedAboveDerivedCompletionFunctor R a).obj Y)
      ((boundedAboveDerivedCompletionFunctor R a).obj Z)).hom ≫
      (𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X) ⊗ₘ μ Y Z) ≫
        μ X (Y ⊗ Z) := by
  let η := boundedAboveDerivedCompletionUnit R a
  have htXY := completionEquivalence_tensorHom R a (η.app X) (η.app Y)
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
    (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj)
  apply boundedAboveCompletionEquivalence_hom_ext R a
    ((η.app X ⊗ₘ η.app Y) ⊗ₘ η.app Z)
    (completionEquivalence_tensorHom R a _ _ htXY
      (derivedComplexCompletionFunctor_map_unit_isIso R a Z.obj))
    (derivedComplexCompletionFunctor_isComplete R a (X ⊗ (Y ⊗ Z)).obj)
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, boundedAboveCompletionTensorComparison_unit]
  rw [associator_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (η.app X ⊗ₘ (η.app Y ⊗ₘ η.app Z)),
    tensorHom_comp_tensorHom, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, boundedAboveCompletionTensorComparison_unit]
  exact (η.naturality (α_ X Y Z).hom).symm

/-- The completion tensor comparison respects the actual symmetry. -/
theorem boundedAboveCompletionTensorComparison_braiding (X Y : D) :
    (β_ ((boundedAboveDerivedCompletionFunctor R a).obj X)
      ((boundedAboveDerivedCompletionFunctor R a).obj Y)).hom ≫ μ Y X =
    μ X Y ≫ (boundedAboveDerivedCompletionFunctor R a).map (β_ X Y).hom := by
  let η := boundedAboveDerivedCompletionUnit R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (η.app X ⊗ₘ η.app Y)
    (completionEquivalence_tensorHom R a _ _
      (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
      (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj))
    (derivedComplexCompletionFunctor_isComplete R a (Y ⊗ X).obj)
  rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
    boundedAboveCompletionTensorComparison_unit, ← Category.assoc,
    boundedAboveCompletionTensorComparison_unit]
  exact η.naturality (β_ X Y).hom

/-- The standard completion unit supplies the left unit of the tensor comparison. -/
theorem boundedAboveCompletionTensorComparison_left_unitality (X : D) :
    (λ_ ((boundedAboveDerivedCompletionFunctor R a).obj X)).hom =
      ((boundedAboveDerivedCompletionUnit R a).app (𝟙_ D) ⊗ₘ
        𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X)) ≫
      μ (𝟙_ D) X ≫ (boundedAboveDerivedCompletionFunctor R a).map (λ_ X).hom := by
  let η := boundedAboveDerivedCompletionUnit R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (𝟙 (𝟙_ D) ⊗ₘ η.app X)
    (completionEquivalence_tensorHom R a _ _ (by
      change IsIso ((derivedComplexCompletionFunctor R a).map (𝟙 (𝟙_ D).obj))
      infer_instance) (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj))
    (derivedComplexCompletionFunctor_isComplete R a X.obj)
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, id_tensorHom, leftUnitor_naturality]
  exact η.naturality (λ_ X).hom

/-- The standard completion unit supplies the right unit of the tensor comparison. -/
theorem boundedAboveCompletionTensorComparison_right_unitality (X : D) :
    (ρ_ ((boundedAboveDerivedCompletionFunctor R a).obj X)).hom =
      (𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X) ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app (𝟙_ D)) ≫
      μ X (𝟙_ D) ≫ (boundedAboveDerivedCompletionFunctor R a).map (ρ_ X).hom := by
  let η := boundedAboveDerivedCompletionUnit R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (η.app X ⊗ₘ 𝟙 (𝟙_ D))
    (completionEquivalence_tensorHom R a _ _
      (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) (by
        change IsIso ((derivedComplexCompletionFunctor R a).map (𝟙 (𝟙_ D).obj))
        infer_instance))
    (derivedComplexCompletionFunctor_isComplete R a X.obj)
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, tensorHom_id, rightUnitor_naturality]
  exact η.naturality (ρ_ X).hom

/-- Actual principal derived completion is lax monoidal via its canonical comparison. -/
@[instance_reducible] def boundedAboveDerivedCompletionLaxMonoidal :
    (boundedAboveDerivedCompletionFunctor R a).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    ((boundedAboveDerivedCompletionUnit R a).app (𝟙_ D))
    (boundedAboveCompletionTensorComparison R a)
    (fun f g ↦ boundedAboveCompletionTensorComparison_naturality R a f g)
    (boundedAboveCompletionTensorComparison_assoc R a)
    (boundedAboveCompletionTensorComparison_left_unitality R a)
    (boundedAboveCompletionTensorComparison_right_unitality R a)

/-- The canonical lax structure also preserves the actual braiding. -/
@[instance_reducible] def boundedAboveDerivedCompletionLaxBraided :
    (boundedAboveDerivedCompletionFunctor R a).LaxBraided where
  toLaxMonoidal := boundedAboveDerivedCompletionLaxMonoidal R a
  braided X Y := (boundedAboveCompletionTensorComparison_braiding R a X Y).symm

/-- The original standard unit is monoidal for the canonical completion tensor structure. -/
theorem boundedAboveDerivedCompletionUnitMonoidal :
    letI := boundedAboveDerivedCompletionLaxMonoidal R a
    NatTrans.IsMonoidal (boundedAboveDerivedCompletionUnit R a) := by
  let := boundedAboveDerivedCompletionLaxMonoidal R a
  constructor
  · exact Category.id_comp _
  · intro X Y
    change 𝟙 (X ⊗ Y) ≫ (boundedAboveDerivedCompletionUnit R a).app (X ⊗ Y) =
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y) ≫ μ X Y
    rw [Category.id_comp, boundedAboveCompletionTensorComparison_unit]

end SerrePositivity.DerivedCompletion
