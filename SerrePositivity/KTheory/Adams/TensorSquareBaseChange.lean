module

public import SerrePositivity.KTheory.Adams.TensorSquare

/-! # Compatibility of tensor base change with the signed symmetry -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open Functor.OplaxMonoidal
variable {R S : Type u} [CommRing R] [CommRing S]

@[reassoc]
lemma extendScalars_braiding_delta (φ : R →+* S) (M N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars φ).map (β_ M N).hom ≫
      δ (ModuleCat.extendScalars φ) N M =
    δ (ModuleCat.extendScalars φ) M N ≫
      (β_ ((ModuleCat.extendScalars φ).obj M) ((ModuleCat.extendScalars φ).obj N)).hom := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl)

@[reassoc]
lemma cochainTensorBaseChangeIso_symmetry (φ : R →+* S)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (cochainTensorSymmetry P Q).hom ≫ (cochainTensorBaseChangeIso φ Q P).hom =
      (cochainTensorBaseChangeIso φ P Q).hom ≫
        (cochainTensorSymmetry (baseChange φ P) (baseChange φ Q)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorBaseChange_hom_ext φ P Q
  intro i j hij
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n hij) ≫
      (ModuleCat.extendScalars φ).map ((cochainTensorSymmetry P Q).hom.f n) ≫
      (cochainTensorBaseChangeXIso φ Q P n).hom =
    (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n hij) ≫
      (cochainTensorBaseChangeXIso φ P Q n).hom ≫
      (cochainTensorSymmetry (baseChange φ P) (baseChange φ Q)).hom.f n
  rw [← Functor.map_comp_assoc, ιTensorObj_cochainTensorSymmetry]
  rw [Functor.map_units_smul, Linear.units_smul_comp, Functor.map_comp_assoc,
    map_ι_cochainTensorBaseChangeXIso]
  rw [map_ι_cochainTensorBaseChangeXIso_assoc,
    ιTensorObj_cochainTensorSymmetry, Linear.comp_units_smul]
  rw [extendScalars_braiding_delta_assoc]
  rfl

namespace Adams

/-- Base change of the tensor square intertwines its signed involution. -/
@[reassoc]
lemma tensorSquareBaseChangeIso_swap (φ : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (tensorSquareSwap P) ≫ (cochainTensorBaseChangeIso φ P P).hom =
      (cochainTensorBaseChangeIso φ P P).hom ≫ tensorSquareSwap (baseChange φ P) :=
  cochainTensorBaseChangeIso_symmetry φ P P

end Adams

end SerrePositivity
