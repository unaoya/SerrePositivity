module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-! # Koszul 符号付きの対称性とホモトピー

## 概要

cochain 複体のテンソル積の Koszul 符号付きの対称性 `cochainTensorSymmetry` を作り、テンソル積がホモトピーとスカラーの零ホモトピーを保つことを示す。

## 方針

対称性は項ごとの符号 (-1)^(ij) 付きの入れ替えで定義し、微分との両立を確かめる。

## 規約

Mathlib の `HomologicalComplex` には Koszul 符号付きの組みひもがない。

## 使われ方

`CochainTensor/Shuffle`、PerfectComplex のテンソル。
-/

@[expose] public noncomputable section

universe u

section CochainTensorSymmetryPart

set_option backward.isDefEq.respectTransparency false
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
attribute [reassoc] ιTensorObj_cochainTensorSymmetry

/-- The signed symmetry is natural in both chain complexes. -/
@[reassoc]
lemma cochainTensorSymmetry_naturality {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap f g ≫ (cochainTensorSymmetry P' Q').hom =
      (cochainTensorSymmetry P Q).hom ≫ cochainTensorMap g f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ιTensorObj_cochainTensorMap_assoc, ιTensorObj_cochainTensorSymmetry,
    ιTensorObj_cochainTensorSymmetry_assoc]
  rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ιTensorObj_cochainTensorMap]
  simp only [BraidedCategory.braiding_naturality_assoc]

end SerrePositivity

end CochainTensorSymmetryPart

section CochainTensorHomotopyPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Tensoring a homotopy in the left variable with a fixed chain map. -/
def cochainTensorHomotopyLeft {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    {f f' : P ⟶ P'} (h : Homotopy f f') (g : Q ⟶ Q') :
    Homotopy (cochainTensorMap f g) (cochainTensorMap f' g) :=
  mapBifunctorMapHomotopy₁ h g (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

/-- Tensoring a homotopy in the right variable with a fixed chain map. -/
def cochainTensorHomotopyRight {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') {g g' : Q ⟶ Q'} (h : Homotopy g g') :
    Homotopy (cochainTensorMap f g) (cochainTensorMap f g') :=
  mapBifunctorMapHomotopy₂ f h (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

@[simp] lemma cochainTensorMap_id (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorMap (𝟙 P) (𝟙 Q) = 𝟙 (cochainTensor P Q) := by
  change (𝟙 P) ⊗ₘ (𝟙 Q) = _
  simp
  rfl

lemma cochainTensorMap_comp {P P' P'' Q Q' Q'' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    cochainTensorMap f g ≫ cochainTensorMap f' g' = cochainTensorMap (f ≫ f') (g ≫ g') := by
  change (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = _
  exact tensorHom_comp_tensorHom _ _ _ _

/-- Homotopy equivalences in both factors give a homotopy equivalence of tensor complexes. -/
def cochainTensorHomotopyEquiv {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv P P') (f : HomotopyEquiv Q Q') :
    HomotopyEquiv (cochainTensor P Q) (cochainTensor P' Q') where
  hom := cochainTensorMap e.hom f.hom
  inv := cochainTensorMap e.inv f.inv
  homotopyHomInvId := by
    rw [cochainTensorMap_comp, ← cochainTensorMap_id]
    exact (cochainTensorHomotopyLeft e.homotopyHomInvId _).trans
      (cochainTensorHomotopyRight _ f.homotopyHomInvId)
  homotopyInvHomId := by
    rw [cochainTensorMap_comp, ← cochainTensorMap_id]
    exact (cochainTensorHomotopyLeft e.homotopyInvHomId _).trans
      (cochainTensorHomotopyRight _ f.homotopyInvHomId)

end SerrePositivity

end CochainTensorHomotopyPart
