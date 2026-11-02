module
public import SerrePositivity.HomologicalAlgebra.TensorConeNaturality
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic

/-! # Tensoring the unit scalar cone with a cochain complex -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]

/-- Tensoring scalar multiplication on the unit identifies it with scalar multiplication. -/
lemma cochainTensorUnitScalar_leftUnitor (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorMap (smulId a (cochainTensorUnit (R := R))) (𝟙 P) ≫
        (cochainTensorLeftUnitor P).hom =
      (cochainTensorLeftUnitor P).hom ≫ smulId a P := by
  rw [smulId, cochainTensorMap_smul_left, cochainTensorMap_id]
  simp [smulId, Linear.smul_comp, Linear.comp_smul]

/-- Tensoring the unit scalar cone with any complex gives its scalar cone. -/
def cochainTensorUnitScalarConeIso (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R)))) P ≅
      (scalarConeFunctor a).obj P :=
  cochainTensorConeLeft (smulId a (cochainTensorUnit (R := R))) P ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩)
      (Arrow.isoMk (cochainTensorLeftUnitor P) (cochainTensorLeftUnitor P)
        (cochainTensorUnitScalar_leftUnitor a P).symm)

@[reassoc]
lemma cochainTensorUnitScalarConeIso_fst (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (cochainTensorUnitScalarConeIso a P).hom.f n ≫
      (mappingCone.fst (smulId a P)).1.v n (n + 1) rfl =
    tensorConeFstX (smulId a (cochainTensorUnit (R := R))) P n ≫
      (cochainTensorLeftUnitor P).hom.f (n + 1) := by
  simp only [cochainTensorUnitScalarConeIso, Iso.trans_hom,
    HomologicalComplex.comp_f, homotopyCofiber.mapArrowIso_hom]
  simp only [Category.assoc]
  change _ ≫ (cochainConeArrowMap
    (cochainTensorMap (smulId a (cochainTensorUnit (R := R))) (𝟙 P))
    (smulId a P)
    (Arrow.isoMk (cochainTensorLeftUnitor P)
      (cochainTensorLeftUnitor P)
      (cochainTensorUnitScalar_leftUnitor a P).symm).hom).f n ≫ _ = _
  rw [cochainConeArrowMap_fst, ← Category.assoc]
  rw [show (cochainTensorConeLeft (smulId a (cochainTensorUnit (R := R))) P).hom.f n ≫
      (mappingCone.fst (cochainTensorMap (smulId a (cochainTensorUnit (R := R)))
        (𝟙 P))).1.v n (n + 1) rfl =
      tensorConeFstX (smulId a (cochainTensorUnit (R := R))) P n from
    tensorConeXIso_hom_fst _ _ n]
  rfl

@[reassoc]
lemma cochainTensorUnitScalarConeIso_snd (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (cochainTensorUnitScalarConeIso a P).hom.f n ≫
      (mappingCone.snd (smulId a P)).v n n (by omega) =
    tensorConeSndX (smulId a (cochainTensorUnit (R := R))) P n ≫
      (cochainTensorLeftUnitor P).hom.f n := by
  simp only [cochainTensorUnitScalarConeIso, Iso.trans_hom,
    HomologicalComplex.comp_f, homotopyCofiber.mapArrowIso_hom]
  simp only [Category.assoc]
  change _ ≫ (cochainConeArrowMap
    (cochainTensorMap (smulId a (cochainTensorUnit (R := R))) (𝟙 P))
    (smulId a P)
    (Arrow.isoMk (cochainTensorLeftUnitor P)
      (cochainTensorLeftUnitor P)
      (cochainTensorUnitScalar_leftUnitor a P).symm).hom).f n ≫ _ = _
  rw [cochainConeArrowMap_snd, ← Category.assoc]
  rw [show (cochainTensorConeLeft (smulId a (cochainTensorUnit (R := R))) P).hom.f n ≫
      (mappingCone.snd (cochainTensorMap (smulId a (cochainTensorUnit (R := R)))
        (𝟙 P))).v n n (by omega) =
      tensorConeSndX (smulId a (cochainTensorUnit (R := R))) P n from
    tensorConeXIso_hom_snd _ _ n]
  rfl

/-- The unit-cone comparison respects every morphism of the other tensor complex. -/
lemma cochainTensorUnitScalarConeIso_naturality (a : R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    cochainTensorMap (𝟙 (CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R))))) f ≫
        (cochainTensorUnitScalarConeIso a Q).hom =
      (cochainTensorUnitScalarConeIso a P).hom ≫ (scalarConeFunctor a).map f := by
  dsimp only [cochainTensorUnitScalarConeIso, Iso.trans_hom,
    homotopyCofiber.mapArrowIso_hom, scalarConeFunctor]
  rw [← Category.assoc, cochainTensorConeLeft_naturality_right]
  simp only [Category.assoc]
  congr 1
  rw [← homotopyCofiber.mapArrowHom_comp, ← homotopyCofiber.mapArrowHom_comp]
  congr 1
  apply Arrow.hom_ext
  · change cochainTensorMap (𝟙 cochainTensorUnit) f ≫ (cochainTensorLeftUnitor Q).hom =
      (cochainTensorLeftUnitor P).hom ≫ f
    exact MonoidalCategory.leftUnitor_naturality f
  · change cochainTensorMap (𝟙 cochainTensorUnit) f ≫ (cochainTensorLeftUnitor Q).hom =
      (cochainTensorLeftUnitor P).hom ≫ f
    exact MonoidalCategory.leftUnitor_naturality f

end SerrePositivity
