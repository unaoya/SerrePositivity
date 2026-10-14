module
public import SerrePositivity.PerfectComplex.TensorPerfect
public import Mathlib.Algebra.Homology.BifunctorFlip

/-! # The Koszul-signed symmetry of integer cochain tensor products -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Apply the ordinary module braiding in each bidegree before totalization. -/
def tensorBicomplexBraidingIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj P).obj Q ≅
      ((((curriedTensor (ModuleCat.{u} R)).flip).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj P).obj Q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents (fun j => β_ (P.X i) (Q.X j)))

/-- Exchange tensor factors, including the Koszul sign of the totalization flip. -/
def cochainTensorSymmetry (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor P Q ≅ cochainTensor Q P :=
  HomologicalComplex₂.total.mapIso (tensorBicomplexBraidingIso P Q) (.up ℤ) ≪≫
    mapBifunctorFlipIso Q P (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

/-- The homogeneous formula for the signed symmetry, in an arbitrary total degree. -/
lemma ιTensorObj_cochainTensorSymmetry (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (cochainTensorSymmetry P Q).hom.f n =
      (i * j).negOnePow • ((β_ (P.X i) (Q.X j)).hom ≫
        ιTensorObj Q P j i n (by omega)) := by
  change ιTensorObj P Q i j n h ≫
    ((HomologicalComplex₂.total.map (tensorBicomplexBraidingIso P Q).hom (.up ℤ)).f n ≫
      (mapBifunctorFlipIso Q P (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).hom.f n) = _
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  rw [ι_mapBifunctorFlipIso_hom]
  simp [tensorBicomplexBraidingIso, mul_comm, Linear.comp_units_smul]

/-- Exchanging factors twice is the identity chain map. -/
lemma cochainTensorSymmetry_hom_comp (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorSymmetry P Q).hom ≫ (cochainTensorSymmetry Q P).hom = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change ιTensorObj P Q i j n h ≫
    ((cochainTensorSymmetry P Q).hom.f n ≫ (cochainTensorSymmetry Q P).hom.f n) =
      ιTensorObj P Q i j n h ≫ 𝟙 _
  rw [← Category.assoc, ιTensorObj_cochainTensorSymmetry]
  rw [Linear.units_smul_comp, Category.assoc, ιTensorObj_cochainTensorSymmetry]
  simp [Linear.comp_units_smul, smul_smul, mul_comm j i]
end SerrePositivity
