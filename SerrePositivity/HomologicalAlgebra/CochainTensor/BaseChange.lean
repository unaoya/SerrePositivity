module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-! # テンソル積の係数変更

## 概要

標準のテンソル積の係数の拡大との比較（二因子と三因子、同次元の公式つき）と、係数の拡大が符号付き対称性を保つことを示す。

## 方針

比較は項ごとのテンソル積の結合と係数の拡大の可換性から作る。

## 規約

単一の複体との場合（CochainTensorBaseChangeSingle）は CochainSingleMonoidal などを挟むので別ファイルのまま。

## 使われ方

PerfectComplex の閉台の K₀ のテンソルの係数変更、KTheory/Adams。
-/

@[expose] public noncomputable section

universe u

section CochainTensorBaseChangePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end CochainTensorBaseChangePart

section CochainTensorBaseChangeSymmetryPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end SerrePositivity

end CochainTensorBaseChangeSymmetryPart

section CochainTensorTripleBaseChangePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex TensorProduct
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Apply the tensor comparison to the outer pair, then to the inner pair. -/
def cochainTensorTripleBaseChangeIso (φ : R →+* S)
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    baseChange φ (cochainTensor (cochainTensor P Q) T) ≅
      cochainTensor (cochainTensor (baseChange φ P) (baseChange φ Q)) (baseChange φ T) :=
  cochainTensorBaseChangeIso φ (cochainTensor P Q) T ≪≫
    cochainTensorIso (cochainTensorBaseChangeIso φ P Q) (Iso.refl _)

/-- Homogeneous summands still detect maps after extension of scalars. -/
lemma cochainTensorTripleBaseChange_hom_ext (φ : R →+* S)
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {Y : ModuleCat.{u} S}
    {f g : (baseChange φ (cochainTensor (cochainTensor P Q) T)).X n ⟶ Y}
    (h : ∀ i j k (hijk : i + j + k = n),
      (ModuleCat.extendScalars φ).map (cochainTensorTripleι P Q T i j k n hijk) ≫ f =
        (ModuleCat.extendScalars φ).map (cochainTensorTripleι P Q T i j k n hijk) ≫ g) :
    f = g := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply cochainTensorTriple_hom_ext P Q T n
  intro i j k hijk
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  exact congrArg ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _) (h i j k hijk)

set_option backward.isDefEq.respectTransparency true in
lemma cochainTensorBaseChangeIso_apply_ι (φ : R →+* S)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j n : ℤ) (h : i + j = n) (x : P.X i) (y : Q.X j) :
    let := φ.toAlgebra
    (cochainTensorBaseChangeIso φ P Q).hom.f n
      ((1 : S) ⊗ₜ[R] ιTensorObj P Q i j n h (x ⊗ₜ[R] y)) =
      ιTensorObj (baseChange φ P) (baseChange φ Q) i j n h
        (((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)) := by
  let := φ.toAlgebra
  have he := congrArg (fun f => f ((1 : S) ⊗ₜ[R] (x ⊗ₜ[R] y)))
    (map_ι_cochainTensorBaseChangeXIso φ P Q i j n h)
  change (cochainTensorBaseChangeXIso φ P Q n).hom
    ((1 : S) ⊗ₜ[R] ιTensorObj P Q i j n h (x ⊗ₜ[R] y)) = _
  change (cochainTensorBaseChangeXIso φ P Q n).hom
    ((1 : S) ⊗ₜ[R] ιTensorObj P Q i j n h (x ⊗ₜ[R] y)) =
      ιTensorObj (baseChange φ P) (baseChange φ Q) i j n h
        (((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)) at he
  exact he

lemma cochainTensorTripleBaseChangeIso_apply_ι (φ : R →+* S)
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    let := φ.toAlgebra
    (cochainTensorTripleBaseChangeIso φ P Q T).hom.f n
      ((1 : S) ⊗ₜ[R] cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      cochainTensorTripleι (baseChange φ P) (baseChange φ Q) (baseChange φ T)
        i j k n h ((((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)) ⊗ₜ[S]
          ((1 : S) ⊗ₜ[R] z)) := by
  let := φ.toAlgebra
  change (cochainTensorMap (cochainTensorBaseChangeIso φ P Q).hom (𝟙 _)).f n
    ((cochainTensorBaseChangeIso φ (cochainTensor P Q) T).hom.f n
      ((1 : S) ⊗ₜ[R] cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))) = _
  rw [cochainTensorTripleι_apply, cochainTensorBaseChangeIso_apply_ι,
    cochainTensorMap_apply_ι, cochainTensorBaseChangeIso_apply_ι]
  rfl

@[reassoc]
lemma cochainTensorTripleBaseChangeIso_rotation (φ : R →+* S)
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (cochainTensorRotationIso P Q T).hom ≫ (cochainTensorTripleBaseChangeIso φ T P Q).hom =
      (cochainTensorTripleBaseChangeIso φ P Q T).hom ≫
        (cochainTensorRotationIso (baseChange φ P) (baseChange φ Q) (baseChange φ T)).hom := by
  let := φ.toAlgebra
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTripleBaseChange_hom_ext φ P Q T n
  intro i j k h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorTripleBaseChangeIso φ T P Q).hom.f n
    ((ModuleCat.extendScalars φ).map ((cochainTensorRotationIso P Q T).hom.f n)
      ((1 : S) ⊗ₜ[R] cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z))) =
    (cochainTensorRotationIso (baseChange φ P) (baseChange φ Q) (baseChange φ T)).hom.f n
      ((cochainTensorTripleBaseChangeIso φ P Q T).hom.f n
        ((1 : S) ⊗ₜ[R] cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))
  rw [ModuleCat.ExtendScalars.map_tmul, cochainTensorRotation_apply_ι,
    cochainTensorTripleBaseChangeIso_apply_ι]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul]
  rw [cochainTensorTripleBaseChangeIso_apply_ι, cochainTensorRotation_apply_ι]
  rfl

end SerrePositivity

end CochainTensorTripleBaseChangePart
