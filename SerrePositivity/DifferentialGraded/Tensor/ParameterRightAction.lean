module
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # 全次数自然変換とbalanced tensorの右作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- Kパラメータの全次数自然変換は右tensor作用と結合的に可換。 -/
lemma paramRightAction {K : Complex A} {M M' : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) (x y : D) :
    (α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom ≫
      (K ◁ rightAction A D M x y) ≫ uncurryRight (a (op x)) =
    (uncurryRight (a (op y)) ▷ (x ⟶[Complex A] y)) ≫ rightAction A D M' x y := by
  apply triple_ext
  intro k r p n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t m f
  change (uncurryRight (a (op x))).f n
    ((K ◁ rightAction A D M x y).f n
      ((α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom.f n
        (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
          (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)))) =
    (rightAction A D M' x y).f n
      ((uncurryRight (a (op y)) ▷ (x ⟶[Complex A] y)).f n
        (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
          (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)))
  rw [associator_apply, whiskerLeft_apply, rightAction_apply,
    whiskerRight_apply, uncurryRight_apply, rightAction_apply]
  rw [uncurryRight_apply]
  simp only [Units.smul_def, map_zsmul]
  change (r * p).negOnePow •
      (((a (op x)).f k t).v (r + p) n (by omega) (moduleAction A M f m rfl)) =
    ((k + r) * p).negOnePow • moduleAction A M' f
      (((a (op y)).f k t).v r (k + r) (by omega) m) hn
  have h := moduleParamNaturality_apply_of_sum A a ha t f m
    (show k + p = k + p from rfl) (show r + (k + p) = n by omega)
    (show r + p = r + p from rfl) (show r + k = k + r by omega)
  rw [h]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

end SerrePositivity.DifferentialGraded.BalancedTensor
