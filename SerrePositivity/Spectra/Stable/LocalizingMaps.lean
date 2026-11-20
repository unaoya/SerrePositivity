module

public import SerrePositivity.Spectra.General.Suspension
public import SerrePositivity.Spectra.General.Evaluation
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-! # Actual stabilization maps between free symmetric spectra

For every A and n this constructs F_(n+1)(A tensor K) -> F_n(A).
The Hom comparison is the actual adjoint bonding map, rather than an assumed
property of a future stable model structure.
-/

@[expose] public section
universe w t v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (K : C)

def localizingGenerator (n : ℕ) (A : C) :
    A ⊗ K ⟶ level ((freeAt (K := K) n).obj A) (n + 1) :=
  (β_ A K).hom ≫ K ◁ freeAtGenerator (K := K) n A ≫
    suspensionMap ((freeAt (K := K) n).obj A) n

def localizingMap (n : ℕ) (A : C) :
    (freeAt (K := K) (n + 1)).obj (A ⊗ K) ⟶ (freeAt (K := K) n).obj A :=
  freeAtLift (n + 1) _ (localizingGenerator K n A)

lemma localizingMap_generator (n : ℕ) (A : C) :
    freeAtGenerator (K := K) (n + 1) (A ⊗ K) ≫
      levelMap (localizingMap K n A) (n + 1) = localizingGenerator K n A :=
  ((freeAtAdjunction (K := K) (n + 1)).homEquiv_unit _ _
    (localizingMap K n A)).symm.trans
      ((freeAtHomEquiv (K := K) (n + 1) _ _).apply_symm_apply _)

lemma localizingMap_hom {E : GeneralSymmetricSpectrum C K} (n : ℕ) (A : C)
    (f : (freeAt (K := K) n).obj A ⟶ E) :
    freeAtHomEquiv (n + 1) (A ⊗ K) E (localizingMap K n A ≫ f) =
      (β_ A K).hom ≫ K ◁ (freeAtHomEquiv n A E f) ≫ suspensionMap E n := by
  have hunit : freeAtHomEquiv (n + 1) (A ⊗ K) E (localizingMap K n A ≫ f) =
      freeAtGenerator (K := K) (n + 1) (A ⊗ K) ≫ levelMap (localizingMap K n A ≫ f) (n + 1) :=
    (freeAtAdjunction (K := K) (n + 1)).homEquiv_unit _ _ _
  have hlevel : levelMap (localizingMap K n A ≫ f) (n + 1) =
      levelMap (localizingMap K n A) (n + 1) ≫ levelMap f (n + 1) := rfl
  rw [hunit, hlevel, ← Category.assoc, localizingMap_generator]
  rw [localizingGenerator, Category.assoc, Category.assoc, suspensionMap_hom]
  have hunit' : freeAtHomEquiv n A E f = freeAtGenerator (K := K) n A ≫ levelMap f n :=
    (freeAtAdjunction (K := K) n).homEquiv_unit A E f
  rw [← whiskerLeft_comp_assoc, ← hunit']

lemma localizingMap_adjoint {E : GeneralSymmetricSpectrum C K} (n : ℕ) (A : C)
    (f : (freeAt (K := K) n).obj A ⟶ E) :
    curry ((β_ K A).hom ≫
      freeAtHomEquiv (n + 1) (A ⊗ K) E (localizingMap K n A ≫ f)) =
      freeAtHomEquiv n A E f ≫ adjointStructureMap E n := by
  rw [localizingMap_hom, ← Category.assoc, SymmetricCategory.symmetry,
    Category.id_comp, curry_natural_left]
  rfl

@[reassoc] lemma localizingMap_naturality (n : ℕ) {A B : C} (f : A ⟶ B) :
    (freeAt (K := K) (n + 1)).map (f ▷ K) ≫ localizingMap K n B =
      localizingMap K n A ≫ (freeAt (K := K) n).map f := by
  apply (freeAtHomEquiv (n + 1) (A ⊗ K) _).injective
  change (freeAtAdjunction (K := K) (n + 1)).homEquiv _ _ _ = _
  rw [(freeAtAdjunction (K := K) (n + 1)).homEquiv_naturality_left]
  change (f ▷ K) ≫ freeAtHomEquiv (n + 1) (B ⊗ K) _ (localizingMap K n B) = _
  have hunit : freeAtHomEquiv (n + 1) (B ⊗ K) _ (localizingMap K n B) =
      freeAtGenerator (K := K) (n + 1) (B ⊗ K) ≫ levelMap (localizingMap K n B) (n + 1) :=
    (freeAtAdjunction (K := K) (n + 1)).homEquiv_unit _ _ _
  have hunit' : freeAtHomEquiv n A _ ((freeAt (K := K) n).map f) =
      freeAtGenerator (K := K) n A ≫ levelMap ((freeAt (K := K) n).map f) n :=
    (freeAtAdjunction (K := K) n).homEquiv_unit _ _ _
  rw [hunit, localizingMap_generator, localizingMap_hom, hunit']
  have hn := (freeAtAdjunction (K := K) n).unit.naturality f
  change f ≫ freeAtGenerator (K := K) n B =
    freeAtGenerator (K := K) n A ≫ levelMap ((freeAt (K := K) n).map f) n at hn
  rw [← hn, localizingGenerator, ← Category.assoc, BraidedCategory.braiding_naturality_left,
    Category.assoc, whiskerLeft_comp, Category.assoc]

def stabilizationMap (n : ℕ) :
    tensorRight K ⋙ freeAt (K := K) (n + 1) ⟶ freeAt (K := K) n where
  app A := localizingMap K n A
  naturality _ _ f := localizingMap_naturality K n f

/-- A genuinely small class of actual stabilization arrows. A may already
be a chosen cofibrant replacement of a small detecting family. -/
def localizingMaps {ι : Type t} (A : ι → C) :
    MorphismProperty (GeneralSymmetricSpectrum C K) :=
  MorphismProperty.ofHoms (fun p : ℕ × ι ↦ localizingMap K p.1 (A p.2))

instance localizingMaps_isSmall {ι : Type t} [Small.{w} ι] (A : ι → C) :
    (localizingMaps K A).IsSmall.{w} := by
  unfold localizingMaps
  infer_instance

end SerrePositivity.SpectrumStabilization
