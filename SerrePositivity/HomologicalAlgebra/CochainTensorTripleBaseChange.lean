module

public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple
public import SerrePositivity.HomologicalAlgebra.CochainTensorBaseChange

/-! # Base change of three tensor factors and homogeneous comparison formulas -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
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
