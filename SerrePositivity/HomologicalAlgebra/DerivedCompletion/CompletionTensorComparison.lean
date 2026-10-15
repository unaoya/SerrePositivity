module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBraided
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletionEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion

/-! # Tensor stability of completion equivalences and the canonical comparison -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Tensoring on the right preserves actual completion equivalences. -/
theorem completionEquivalence_whiskerRight {X Y : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom)) (Z : D) :
    IsIso ((derivedComplexCompletionFunctor R a).map (f ▷ Z).hom) := by
  apply boundedAboveCompletion_map_isIso_of_koszul R a
  intro n
  apply (boundedAboveDerivedTensorKoszul_isIso_iff (a ^ n) (f ▷ Z)).mp
  have : IsIso (boundedAboveKoszulObject (a ^ n) ◁ f) :=
    (boundedAboveDerivedTensorKoszul_isIso_iff (a ^ n) f).mpr
      (derivedScalarCone_map_isIso_of_completion R a f.hom hf n)
  rw [whisker_assoc_symm]
  infer_instance

/-- Tensoring on the left preserves actual completion equivalences. -/
theorem completionEquivalence_whiskerLeft {X Y : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom)) (Z : D) :
    IsIso ((derivedComplexCompletionFunctor R a).map (Z ◁ f).hom) := by
  have := completionEquivalence_whiskerRight R a f hf Z
  have he : Z ◁ f = (β_ Z X).hom ≫ (f ▷ Z) ≫ (β_ Z Y).inv := by
    apply (cancel_mono (β_ Z Y).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact BraidedCategory.braiding_naturality_right Z f
  rw [he, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Tensoring two completion equivalences again gives a completion equivalence. -/
theorem completionEquivalence_tensorHom {X Y U V : D} (f : X ⟶ Y) (g : U ⟶ V)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom))
    (hg : IsIso ((derivedComplexCompletionFunctor R a).map g.hom)) :
    IsIso ((derivedComplexCompletionFunctor R a).map (f ⊗ₘ g).hom) := by
  have := completionEquivalence_whiskerRight R a f hf U
  have := completionEquivalence_whiskerLeft R a g hg Y
  rw [tensorHom_def, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  infer_instance

/-- Completion inverts the tensor product of its two actual standard units. -/
theorem boundedAboveCompletion_tensor_unit_isIso (X Y : D) :
    IsIso ((boundedAboveDerivedCompletionFunctor R a).map
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y)) := by
  have h := completionEquivalence_tensorHom R a
    ((boundedAboveDerivedCompletionUnit R a).app X)
    ((boundedAboveDerivedCompletionUnit R a).app Y)
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
    (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj)
  have : IsIso (DerivedCategory.Minus.ι.map ((boundedAboveDerivedCompletionFunctor R a).map
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y))) := h
  exact isIso_of_reflects_iso _ DerivedCategory.Minus.ι

/-- The canonical lax tensor comparison, built from the original standard unit. -/
def boundedAboveCompletionTensorComparison (X Y : D) :
    (boundedAboveDerivedCompletionFunctor R a).obj X ⊗
        (boundedAboveDerivedCompletionFunctor R a).obj Y ⟶
      (boundedAboveDerivedCompletionFunctor R a).obj (X ⊗ Y) := by
  have := boundedAboveCompletion_tensor_unit_isIso R a X Y
  exact (boundedAboveDerivedCompletionUnit R a).app _ ≫
    inv ((boundedAboveDerivedCompletionFunctor R a).map
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y))

/-- The comparison extends the original tensor product of standard units. -/
theorem boundedAboveCompletionTensorComparison_unit (X Y : D) :
    ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
      (boundedAboveDerivedCompletionUnit R a).app Y) ≫
        boundedAboveCompletionTensorComparison R a X Y =
      (boundedAboveDerivedCompletionUnit R a).app (X ⊗ Y) := by
  have := boundedAboveCompletion_tensor_unit_isIso R a X Y
  let t := (boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
    (boundedAboveDerivedCompletionUnit R a).app Y
  have ht := (boundedAboveDerivedCompletionUnit R a).naturality t
  change t ≫ (boundedAboveDerivedCompletionUnit R a).app _ =
    (boundedAboveDerivedCompletionUnit R a).app _ ≫
      (boundedAboveDerivedCompletionFunctor R a).map t at ht
  change t ≫ ((boundedAboveDerivedCompletionUnit R a).app _ ≫
    inv ((boundedAboveDerivedCompletionFunctor R a).map t)) = _
  rw [← Category.assoc, ht, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- Maps to a complete target are determined along any completion equivalence. -/
theorem completionEquivalence_hom_ext
    {X Y Z : ConcreteDerivedCategory R} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f))
    (hZ : IsComplete R a Z) {g h : Y ⟶ Z} (he : f ≫ g = f ≫ h) : g = h := by
  have := hf
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a Z hZ
  have hm : (derivedComplexCompletionFunctor R a).map g =
      (derivedComplexCompletionFunctor R a).map h := by
    apply (cancel_epi ((derivedComplexCompletionFunctor R a).map f)).mp
    simpa only [← Functor.map_comp] using
      congrArg (derivedComplexCompletionFunctor R a).map he
  apply (cancel_mono ((derivedComplexCompletionUnit R a).app Z)).mp
  have hg := (derivedComplexCompletionUnit R a).naturality g
  have hh := (derivedComplexCompletionUnit R a).naturality h
  simp only [Functor.id_map] at hg hh
  rw [hg, hh, hm]

/-- The same uniqueness criterion inside the bounded-above category. -/
theorem boundedAboveCompletionEquivalence_hom_ext
    {X Y Z : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom))
    (hZ : IsComplete R a Z.obj) {g h : Y ⟶ Z} (he : f ≫ g = f ≫ h) : g = h := by
  apply InducedCategory.hom_ext
  apply completionEquivalence_hom_ext R a f.hom hf hZ
  exact congrArg (fun k ↦ k.hom) he

/-- The canonical comparison is natural in both tensor factors. -/
theorem boundedAboveCompletionTensorComparison_naturality
    {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((boundedAboveDerivedCompletionFunctor R a).map f ⊗ₘ
      (boundedAboveDerivedCompletionFunctor R a).map g) ≫
        boundedAboveCompletionTensorComparison R a X' Y' =
      boundedAboveCompletionTensorComparison R a X Y ≫
        (boundedAboveDerivedCompletionFunctor R a).map (f ⊗ₘ g) := by
  let η := boundedAboveDerivedCompletionUnit R a
  let L := boundedAboveDerivedCompletionFunctor R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (η.app X ⊗ₘ η.app Y)
    (completionEquivalence_tensorHom R a _ _
      (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
      (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj))
    (derivedComplexCompletionFunctor_isComplete R a (X' ⊗ Y').obj)
  have hf := η.naturality f
  have hg := η.naturality g
  simp only [Functor.id_map] at hf hg
  have ht : (η.app X ⊗ₘ η.app Y) ≫ (L.map f ⊗ₘ L.map g) =
      (f ⊗ₘ g) ≫ (η.app X' ⊗ₘ η.app Y') := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ← hf, ← hg]
  rw [← Category.assoc, ht, Category.assoc, boundedAboveCompletionTensorComparison_unit,
    ← Category.assoc, boundedAboveCompletionTensorComparison_unit]
  exact η.naturality (f ⊗ₘ g)

end SerrePositivity.DerivedCompletion
