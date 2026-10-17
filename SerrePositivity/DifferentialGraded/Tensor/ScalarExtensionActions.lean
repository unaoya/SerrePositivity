module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Tensor.Actions

/-! # 係数変更と balanced tensor の左右作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma leftModule_action (N : LeftModule A D) (x y : D) (p r n : ℤ)
    (h : r + p = n) (f : GradedHom A x y p) (m : (N.obj x).X r) :
    let := φ.toAlgebra
    leftAction A' (leftModule φ D N) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) h =
      (1 : A') ⊗ₜ[A] leftAction A N f m h := by
  let := φ.toAlgebra
  change ((homComparison φ (N.obj x) (N.obj y)).f p
    ((ModuleCat.extendScalars φ).map ((N.map x y).f p) ((1 : A') ⊗ₜ[A] f))).v r n h
      ((1 : A') ⊗ₜ[A] m) = _
  erw [ModuleCat.ExtendScalars.map_tmul φ, homComparison_apply φ (N.obj x) (N.obj y) p r n h]
  rfl

@[reassoc]
lemma rightAction_comparison (M : RightModule A D) (x y : D) :
    (extension φ).map (BalancedTensor.rightAction A D M x y) =
      (tensorIso φ (M.obj (op y)) (homObject A D x y)).hom ≫
        BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (M.obj (op y)) (homObject A D x y)
  intro r p h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m f
  change (ModuleCat.extendScalars φ).map ((BalancedTensor.rightAction A D M x y).f n)
    ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op y)) (homObject A D x y) r p n h (m ⊗ₜ[A] f)) =
    (BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y).f n
      ((tensorIso φ (M.obj (op y)) (homObject A D x y)).hom.f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op y)) (homObject A D x y) r p n h (m ⊗ₜ[A] f)))
  erw [ModuleCat.ExtendScalars.map_tmul φ, BalancedTensor.rightAction_apply,
    cochainTensorBaseChangeIso_apply_ι φ (M.obj (op y)) (homObject A D x y),
    BalancedTensor.rightAction_apply,
    rightModule_action φ D M (op y) (op x) p r n h f m]
  simp only [Units.smul_def, TensorProduct.tmul_smul]
  rfl

@[reassoc]
lemma leftAction_comparison (N : LeftModule A D) (x y : D) :
    (extension φ).map (BalancedTensor.leftAction A D N x y) =
      (tensorIso φ (homObject A D x y) (N.obj x)).hom ≫
        BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (homObject A D x y) (N.obj x)
  intro p r h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f m
  change (ModuleCat.extendScalars φ).map ((BalancedTensor.leftAction A D N x y).f n)
    ((1 : A') ⊗ₜ[A] ιTensorObj (homObject A D x y) (N.obj x) p r n h (f ⊗ₜ[A] m)) =
    (BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y).f n
      ((tensorIso φ (homObject A D x y) (N.obj x)).hom.f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (homObject A D x y) (N.obj x) p r n h (f ⊗ₜ[A] m)))
  erw [ModuleCat.ExtendScalars.map_tmul φ, BalancedTensor.leftAction_apply,
    cochainTensorBaseChangeIso_apply_ι φ (homObject A D x y) (N.obj x),
    BalancedTensor.leftAction_apply,
    leftModule_action φ D N x y p r n (by omega) f m]

end SerrePositivity.DifferentialGraded.ScalarExtension
