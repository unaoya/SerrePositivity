module
public import SerrePositivity.HomologicalAlgebra.CochainTensor
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Base change of the standard cochain tensor product -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open Functor.Monoidal Functor.OplaxMonoidal
variable {R S : Type u} [CommRing R] [CommRing S]
variable (φ : R →+* S) (P Q : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Extend scalars through the total coproduct, then through each tensor summand. -/
def cochainTensorBaseChangeXIso (n : ℤ) :
    (baseChange φ (cochainTensor P Q)).X n ≅
      (cochainTensor (baseChange φ P) (baseChange φ Q)).X n :=
  (asIso (sigmaComparison (ModuleCat.extendScalars φ) (cochainTensorSummand P Q n))).symm ≪≫
    Sigma.mapIso (fun ij => (μIso (ModuleCat.extendScalars φ) (P.X ij.val.1) (Q.X ij.val.2)).symm)

/-- The homogeneous formula for the base-change comparison. -/
@[reassoc]
lemma map_ι_cochainTensorBaseChangeXIso (i j n : ℤ) (h : i + j = n) :
    (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n h) ≫
        (cochainTensorBaseChangeXIso φ P Q n).hom =
      δ (ModuleCat.extendScalars φ) (P.X i) (Q.X j) ≫
        ιTensorObj (baseChange φ P) (baseChange φ Q) i j n h := by
  let F := ModuleCat.extendScalars φ
  change F.map (Sigma.ι (cochainTensorSummand P Q n) ⟨(i, j), h⟩) ≫
    (inv (sigmaComparison F (cochainTensorSummand P Q n)) ≫
      (Sigma.mapIso (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
        (μIso F (P.X ij.val.1) (Q.X ij.val.2)).symm)).hom) = _
  rw [← Category.assoc, map_ι_comp_inv_sigmaComparison, Sigma.ι_mapIso_hom]
  rfl

/-- Images of homogeneous summands detect morphisms out of the base-changed tensor. -/
lemma cochainTensorBaseChange_hom_ext {n : ℤ} {T : ModuleCat.{u} S}
    {f g : (baseChange φ (cochainTensor P Q)).X n ⟶ T}
    (h : ∀ (i j : ℤ) (hij : i + j = n),
      (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n hij) ≫ f =
        (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n hij) ≫ g) : f = g := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (ModuleCat.extendScalars φ) (cochainTensorSummand P Q n)).hom_ext
  intro ij
  exact h ij.as.val.1 ij.as.val.2 ij.as.property

/-- Base change of a tensor complex is the tensor of the two base-changed complexes. -/
def cochainTensorBaseChangeIso :
    baseChange φ (cochainTensor P Q) ≅ cochainTensor (baseChange φ P) (baseChange φ Q) :=
  HomologicalComplex.Hom.isoOfComponents (cochainTensorBaseChangeXIso φ P Q) (by
    intro n m h
    dsimp at h
    subst m
    apply cochainTensorBaseChange_hom_ext φ P Q
    intro i j hij
    rw [map_ι_cochainTensorBaseChangeXIso_assoc]
    rw [ιTensorObj_cochainTensor_d]
    simp only [baseChange, Functor.mapHomologicalComplex_obj_d,
      Functor.mapHomologicalComplex_obj_X]
    rw [← Functor.map_comp_assoc, ιTensorObj_cochainTensor_d]
    rw [Functor.map_add, Functor.map_units_smul, Preadditive.add_comp, Linear.units_smul_comp]
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc,
      map_ι_cochainTensorBaseChangeXIso, map_ι_cochainTensorBaseChangeXIso]
    simp only [Preadditive.comp_add, Linear.comp_units_smul]
    simp only [δ_natural_left_assoc, δ_natural_right_assoc])

end SerrePositivity
