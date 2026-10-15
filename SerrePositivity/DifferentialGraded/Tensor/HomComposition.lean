module
public import SerrePositivity.DifferentialGraded.Tensor.HomUnits
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition
public import SerrePositivity.DifferentialGraded.Functor.ComplexValued

/-! # balanced tensorの主Hom写像の合成保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma rightHomMap_forward {M M' M'' : RightModule A D} (N : LeftModule A D)
    {p q k : ℤ} (τ : (moduleHom A D M M').X p) (σ : (moduleHom A D M' M'').X q)
    (hk : p + q = k) :
    (rightHomMap A D M M'' N).f k
      (forward A (D := RightModule A D) (x := M) (y := M') (z := M'') τ σ hk) =
      forward A (D := Complex A) (x := obj A D M N) (y := obj A D M' N)
        (z := obj A D M'' N) ((rightHomMap A D M M' N).f p τ)
        ((rightHomMap A D M' M'' N).f q σ) hk := by
  change _ = (enrichedComposition (obj A D M N) (obj A D M' N) (obj A D M'' N)).f k
    (ιTensorObj (homComplex A (obj A D M N) (obj A D M' N))
      (homComplex A (obj A D M' N) (obj A D M'' N)) p q k hk
      (((rightHomMap A D M M' N).f p τ) ⊗ₜ[A] ((rightHomMap A D M' M'' N).f q σ)))
  rw [enrichedComposition_apply]
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [rightHomMap_element_of_sum A D N _ x m v ha (show k + r = q + (p + r) by omega) hn,
    moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hk r (p + r) (q + (p + r)) (by omega) (by omega),
    Cochain.units_smul_v,
    Cochain.comp_v _ _ hk a (p + r + s) n (by omega) (by omega)]
  change element A D M'' N x
      ((p * q).negOnePow • (((moduleHomπ A D M' M'' x).f q σ).v (p + r)
        (q + (p + r)) (by omega)
        (((moduleHomπ A D M M' x).f p τ).v r (p + r) (by omega) m))) v (by omega) =
    (p * q).negOnePow • (((rightHomMap A D M' M'' N).f q σ).v (p + r + s) n
      (by omega) ((((rightHomMap A D M M' N).f p τ).v a (p + r + s) (by omega))
        (element A D M N x m v ha)))
  rw [rightHomMap_element_of_sum A D N τ x m v ha rfl (by omega),
    rightHomMap_element_of_sum A D N σ x _ v rfl rfl (by omega)]
  simp only [element, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]

lemma leftModuleHomForward_π {N N' N'' : LeftModule A D} {p q k : ℤ}
    (τ : (leftModuleHom A D N N').X p) (σ : (leftModuleHom A D N' N'').X q)
    (hk : p + q = k) (x : D) :
    (leftModuleHomπ A D N N'' x).f k
      (forward A (D := LeftModule A D) (x := N) (y := N') (z := N'') τ σ hk) =
    (p * q).negOnePow • (((leftModuleHomπ A D N N' x).f p τ).comp
      ((leftModuleHomπ A D N' N'' x).f q σ) hk) :=
  DGFunctor.map_forward_cochain A (leftModuleEvaluationDG A D x) τ σ hk

lemma leftHomMap_forward (M : RightModule A D) {N N' N'' : LeftModule A D}
    {p q k : ℤ} (τ : (leftModuleHom A D N N').X p) (σ : (leftModuleHom A D N' N'').X q)
    (hk : p + q = k) :
    (leftHomMap A D M N N'').f k
      (forward A (D := LeftModule A D) (x := N) (y := N') (z := N'') τ σ hk) =
    forward A (D := Complex A) (x := obj A D M N) (y := obj A D M N')
      (z := obj A D M N'') ((leftHomMap A D M N N').f p τ)
        ((leftHomMap A D M N' N'').f q σ) hk := by
  change _ = (enrichedComposition (obj A D M N) (obj A D M N') (obj A D M N'')).f k
    (ιTensorObj (homComplex A (obj A D M N) (obj A D M N'))
      (homComplex A (obj A D M N') (obj A D M N'')) p q k hk
      (((leftHomMap A D M N N').f p τ) ⊗ₜ[A] ((leftHomMap A D M N' N'').f q σ)))
  rw [enrichedComposition_apply]
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [leftHomMap_element_of_sum A D M _ x m v ha (show k + s = q + (p + s) by omega) hn,
    leftModuleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hk s (p + s) (q + (p + s)) (by omega) (by omega),
    Cochain.units_smul_v,
    Cochain.comp_v _ _ hk a (r + (p + s)) n (by omega) (by omega)]
  change (k * r).negOnePow • element A D M N'' x m
      ((p * q).negOnePow • (((leftModuleHomπ A D N' N'' x).f q σ).v (p + s)
        (q + (p + s)) (by omega) (((leftModuleHomπ A D N N' x).f p τ).v s (p + s)
          (by omega) v))) (by omega) =
    (p * q).negOnePow • (((leftHomMap A D M N' N'').f q σ).v (r + (p + s)) n
      (by omega) ((((leftHomMap A D M N N').f p τ).v a (r + (p + s)) (by omega))
        (element A D M N x m v ha)))
  rw [element_units_smul_right,
    leftHomMap_element_of_sum A D M τ x m v ha rfl (by omega)]
  simp only [Units.smul_def, map_zsmul]
  change (k * r).negOnePow • ((p * q).negOnePow • _) =
    (p * q).negOnePow • ((p * r).negOnePow •
      (((leftHomMap A D M N' N'').f q σ).v (r + (p + s)) n (by omega)
        (element A D M N' x m
          (((leftModuleHomπ A D N N' x).f p τ).v s (p + s) (by omega) v) rfl)))
  rw [leftHomMap_element_of_sum A D M σ x m _ rfl rfl (by omega)]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  rw [← hk]
  ring

end SerrePositivity.DifferentialGraded.BalancedTensor
