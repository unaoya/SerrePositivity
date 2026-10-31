module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionColimits
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation

/-! # 係数変更の tensor 比較の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types true
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 任意の整数次数に置いた係数環の係数変更。 -/
def sphereIso (n : ℤ) :
    (extension φ).obj (complexSphere A n) ≅ complexSphere A' n :=
  (singleMapHomologicalComplex (ModuleCat.extendScalars φ) (.up ℤ) n).app _ ≪≫
    (single (ModuleCat A') (.up ℤ) n).mapIso
      (Functor.Monoidal.εIso (ModuleCat.extendScalars φ)).symm

/-- 単位複体との比較。 -/
abbrev unitIso : (extension φ).obj (𝟙_ (Complex A)) ≅ 𝟙_ (Complex A') := sphereIso φ 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma sphereIso_one (n : ℤ) :
    let := φ.toAlgebra
    (sphereIso φ n).hom.f n
      ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv (1 : A)) =
        (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A'))).inv (1 : A') := by
  let := φ.toAlgebra
  simp only [sphereIso, Iso.trans_hom, comp_f]
  erw [single_map_f_self]
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, Iso.app_hom,
    singleMapHomologicalComplex_hom_app_self, Iso.symm_hom, Functor.Monoidal.εIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.ExtendScalars.map_tmul, Iso.inv_hom_id_apply]
  rw [ModuleCat.extendScalars_η]
  erw [TensorProduct.AlgebraTensorModule.rid_tmul (R := A) (A := A') (M := A') (1 : A) (1 : A')]
  simp

set_option maxHeartbeats 800000 in
-- 各次数での係数変更と total tensor の型の展開に必要。
lemma tensorIso_left_unitor (K : Complex A) :
    (λ_ ((extension φ).obj K)).inv = (extension φ).map (λ_ K).inv ≫
      (tensorIso φ (𝟙_ (Complex A)) K).hom ≫ (unitIso φ).hom ▷ (extension φ).obj K := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (λ_ ((extension φ).obj K)).inv.f n ((1 : A') ⊗ₜ[A] x) =
    (cochainTensorMap (unitIso φ).hom (𝟙 _)).f n
      ((tensorIso φ (𝟙_ (Complex A)) K).hom.f n
        ((ModuleCat.extendScalars φ).map ((λ_ K).inv.f n) ((1 : A') ⊗ₜ[A] x)))
  erw [ModuleCat.ExtendScalars.map_tmul φ]
  simp only [complexLeftUnitor_inv_apply]
  dsimp only [tensorIso]
  erw [cochainTensorBaseChangeIso_apply_ι φ (𝟙_ (Complex A)) K 0 n n (zero_add n)
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) x]
  erw [cochainTensorMap_apply_ι (unitIso φ).hom (𝟙 ((extension φ).obj K))]
  erw [sphereIso_one φ]
  convert complexLeftUnitor_inv_apply ((extension φ).obj K) n ((1 : A') ⊗ₜ[A] x) using 1; rfl

set_option maxHeartbeats 800000 in
-- 各次数での係数変更と total tensor の型の展開に必要。
lemma tensorIso_right_unitor (K : Complex A) :
    (ρ_ ((extension φ).obj K)).inv = (extension φ).map (ρ_ K).inv ≫
      (tensorIso φ K (𝟙_ (Complex A))).hom ≫ (extension φ).obj K ◁ (unitIso φ).hom := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (ρ_ ((extension φ).obj K)).inv.f n ((1 : A') ⊗ₜ[A] x) =
    (cochainTensorMap (𝟙 _) (unitIso φ).hom).f n
      ((tensorIso φ K (𝟙_ (Complex A))).hom.f n
        ((ModuleCat.extendScalars φ).map ((ρ_ K).inv.f n) ((1 : A') ⊗ₜ[A] x)))
  erw [ModuleCat.ExtendScalars.map_tmul φ]
  simp only [complexRightUnitor_inv_apply]
  dsimp only [tensorIso]
  erw [cochainTensorBaseChangeIso_apply_ι φ K (𝟙_ (Complex A)) n 0 n (add_zero n)
    x ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))]
  erw [cochainTensorMap_apply_ι (𝟙 ((extension φ).obj K)) (unitIso φ).hom]
  erw [sphereIso_one φ]
  convert complexRightUnitor_inv_apply ((extension φ).obj K) n ((1 : A') ⊗ₜ[A] x) using 1; rfl

set_option maxHeartbeats 1600000 in
-- 三重 total tensor の成分を展開して比較する。
@[reassoc]
lemma tensorIso_associator (K L M : Complex A) :
    (tensorIso φ (K ⊗ L) M).hom ≫ (tensorIso φ K L).hom ▷ (extension φ).obj M ≫
        (α_ ((extension φ).obj K) ((extension φ).obj L) ((extension φ).obj M)).hom =
      (extension φ).map (α_ K L M).hom ≫ (tensorIso φ K (L ⊗ M)).hom ≫
        (extension φ).obj K ◁ (tensorIso φ L M).hom := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorTripleBaseChange_hom_ext φ K L M n
  intro i j k h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change (cochainTensorAssociator _ _ _).hom.f n
    ((cochainTensorMap (tensorIso φ K L).hom (𝟙 _)).f n
      ((tensorIso φ (K ⊗ L) M).hom.f n
        ((1 : A') ⊗ₜ[A] cochainTensorTripleι K L M i j k n h ((x ⊗ₜ[A] y) ⊗ₜ[A] z)))) =
    (cochainTensorMap (𝟙 _) (tensorIso φ L M).hom).f n
      ((tensorIso φ K (L ⊗ M)).hom.f n
        ((ModuleCat.extendScalars φ).map ((cochainTensorAssociator K L M).hom.f n)
          ((1 : A') ⊗ₜ[A] cochainTensorTripleι K L M i j k n h ((x ⊗ₜ[A] y) ⊗ₜ[A] z))))
  dsimp only [tensorIso]
  erw [cochainTensorTripleι_apply]
  erw [cochainTensorBaseChangeIso_apply_ι φ (K ⊗ L) M (i + j) k n h
    (ιTensorObj K L i j (i + j) rfl (x ⊗ₜ[A] y)) z]
  erw [cochainTensorMap_apply_ι]
  erw [cochainTensorBaseChangeIso_apply_ι φ K L i j (i + j) rfl x y]
  erw [cochainTensorAssociator_hom_apply_ι]
  erw [ModuleCat.ExtendScalars.map_tmul φ, cochainTensorAssociator_hom_apply_ι]
  erw [cochainTensorBaseChangeIso_apply_ι φ K (L ⊗ M) i (j + k) n (by omega)
    x (ιTensorObj L M j k (j + k) rfl (y ⊗ₜ[A] z))]
  erw [cochainTensorMap_apply_ι]
  erw [cochainTensorBaseChangeIso_apply_ι φ L M j k (j + k) rfl y z]
  rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
