module

public import SerrePositivity.HomotopicalAlgebra.Replacement.FibrantCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor

/-! # Small Kan mapping spaces on actual source and target replacement presentations

Both projections retain arbitrary base objects. Strict maps retain actual
replacement comparisons; no functorial section of either projection is assumed.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.ModelReplacement

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev hom : (FramedResolution C)ᵒᵖ ⥤ FibrantReplacementObject C ⥤ SSet.{v} :=
  FramedResolution.hom hcof hfib ⋙
    (Functor.whiskeringLeft (FibrantReplacementObject C) C SSet.{v}).obj
      FibrantReplacementObject.targets

abbrev raw : (FramedResolution C)ᵒᵖ ⥤ FibrantReplacementObject C ⥤ SSet.{v} :=
  FramedResolution.raw ⋙
    (Functor.whiskeringLeft (FibrantReplacementObject C) C SSet.{v}).obj
      FibrantReplacementObject.targets

/-- The identity presentations of fibrant targets recover the previous strict bifunctor. -/
lemma fibrant_restriction :
    hom (C := C) hcof hfib ⋙
      (Functor.whiskeringLeft (FibrantObject C) (FibrantReplacementObject C) SSet.{v}).obj
        FibrantReplacementObject.fromFibrant = FramedResolution.fibrantHom hcof hfib := rfl

/-- A comparison of the entire strict presentation bifunctors. -/
def comparison : raw (C := C) ⟶ hom hcof hfib :=
  Functor.whiskerRight (FramedResolution.comparison hcof hfib)
    ((Functor.whiskeringLeft (FibrantReplacementObject C) C SSet.{v}).obj
      FibrantReplacementObject.targets)

lemma comparison_weakEquivalence (X : (FramedResolution C)ᵒᵖ)
    (Y : FibrantReplacementObject C) :
    weakEquivalences SSet.{v} (((comparison hcof hfib).app X).app Y) :=
  FramedResolution.comparison_weakEquivalence hcof hfib X Y.obj

lemma kanComplex (X : (FramedResolution C)ᵒᵖ) (Y : FibrantReplacementObject C) :
    SSet.KanComplex (((hom hcof hfib).obj X).obj Y) :=
  FramedResolution.hom_kanComplex hcof hfib X Y.obj

lemma source_weakEquivalence {X X' : (FramedResolution C)ᵒᵖ} (f : X ⟶ X')
    (hf : weakEquivalences C f.unop.map.base) (Y : FibrantReplacementObject C) :
    weakEquivalences SSet.{v} (((hom hcof hfib).map f).app Y) :=
  FramedResolution.hom_source_weakEquivalence hcof hfib f hf Y.obj

lemma target_weakEquivalence (X : (FramedResolution C)ᵒᵖ)
    {Y Y' : FibrantReplacementObject C} (f : Y ⟶ Y') (hf : weakEquivalences C f.base) :
    weakEquivalences SSet.{v} (((hom hcof hfib).obj X).map f) :=
  FramedResolution.hom_target_weakEquivalence hcof hfib X f.map
    ((FibrantReplacementObject.map_weakEquivalence_iff f).mpr hf)

/-- Any two actual target replacement presentations are joined over the identity base map. -/
lemma target_choice_weakEquivalence (X : (FramedResolution C)ᵒᵖ)
    (Y Y' : FibrantReplacementObject C) (e : Y.base ≅ Y'.base) :
    weakEquivalences SSet.{v}
      (((hom hcof hfib).obj X).map (FibrantReplacementObject.liftBase e.hom)) :=
  target_weakEquivalence hcof hfib X _ ((weakEquivalences C).of_isIso e.hom)

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

/-- The actual replacement inclusion is inverted by the specified ordinary localization. -/
def baseIso (Y : FibrantReplacementObject C) : Q.obj Y.base ≅ Q.obj Y.obj := by
  have : IsIso (Q.map Y.inclusion) :=
    Localization.inverts Q (weakEquivalences C) _ Y.trivial.2
  exact asIso (Q.map Y.inclusion)

omit [ModelCategory SSet.{v}] in
lemma baseIso_naturality {Y Y' : FibrantReplacementObject C} (f : Y ⟶ Y') :
    (baseIso Q Y).hom ≫ Q.map f.map = Q.map f.base ≫ (baseIso Q Y').hom := by
  change Q.map Y.inclusion ≫ Q.map f.map = Q.map f.base ≫ Q.map Y'.inclusion
  rw [← Q.map_comp, f.under, Q.map_comp]

omit [ModelCategory SSet.{v}] in
lemma baseIso_inv_naturality {Y Y' : FibrantReplacementObject C} (f : Y ⟶ Y') :
    Q.map f.map ≫ (baseIso Q Y').inv = (baseIso Q Y).inv ≫ Q.map f.base := by
  apply (cancel_mono (baseIso Q Y').hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    ← baseIso_naturality, Iso.inv_hom_id_assoc]

/-- Components refer to the original, possibly nonfibrant, target base object. -/
def piZeroEquiv (X : (FramedResolution C)ᵒᵖ) (Y : FibrantReplacementObject C) :
    SSet.π₀ (((hom hcof hfib).obj X).obj Y) ≃
      (Q.obj X.unop.inner.base ⟶ Q.obj Y.base) where
  toFun z := FramedResolution.piZeroEquiv hcof hfib Q X Y.obj z ≫ (baseIso Q Y).inv
  invFun z := (FramedResolution.piZeroEquiv hcof hfib Q X Y.obj).symm
    (z ≫ (baseIso Q Y).hom)
  left_inv z := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Equiv.symm_apply_apply]
  right_inv z := by simp only [Equiv.apply_symm_apply, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma piZero_naturality_source {X X' : (FramedResolution C)ᵒᵖ} (f : X ⟶ X')
    (Y : FibrantReplacementObject C) (z : SSet.π₀ (((hom hcof hfib).obj X).obj Y)) :
    piZeroEquiv hcof hfib Q X' Y (SSet.mapπ₀ (((hom hcof hfib).map f).app Y) z) =
      Q.map f.unop.map.base ≫ piZeroEquiv hcof hfib Q X Y z := by
  change FramedResolution.piZeroEquiv hcof hfib Q X' Y.obj
    (SSet.mapπ₀ (((FramedResolution.hom hcof hfib).map f).app Y.obj) z) ≫ _ = _
  rw [FramedResolution.piZero_naturality_source, Category.assoc]
  rfl

lemma piZero_naturality_target (X : (FramedResolution C)ᵒᵖ)
    {Y Y' : FibrantReplacementObject C} (f : Y ⟶ Y')
    (z : SSet.π₀ (((hom hcof hfib).obj X).obj Y)) :
    piZeroEquiv hcof hfib Q X Y' (SSet.mapπ₀ (((hom hcof hfib).obj X).map f) z) =
      piZeroEquiv hcof hfib Q X Y z ≫ Q.map f.base := by
  have h := FramedResolution.piZero_naturality_target hcof hfib Q X
    ((FibrantReplacementObject.fibrantTargets (C := C)).map f) z
  exact (congrArg (fun a => a ≫ (baseIso Q Y').inv) h).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => FramedResolution.piZeroEquiv hcof hfib Q X Y.obj z ≫ a)
        (baseIso_inv_naturality Q f)).trans (Category.assoc _ _ _).symm))

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
