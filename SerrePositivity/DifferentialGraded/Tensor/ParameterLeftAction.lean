module
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Module.LeftParamNaturality

/-! # 全次数自然変換と左tensor作用の交換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma paramLeftAction {K : Complex A} {N N' : LeftModule A D}
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) (x y : D) :
    (α_ K (x ⟶[Complex A] y) (N.obj x)).hom ≫
      (K ◁ leftAction A D N x y) ≫ uncurryRight (a y) =
    ((signedSwap K (x ⟶[Complex A] y)).hom ▷ N.obj x) ≫
      (α_ (x ⟶[Complex A] y) K (N.obj x)).hom ≫
        ((x ⟶[Complex A] y) ◁ uncurryRight (a x)) ≫ leftAction A D N' x y := by
  apply triple_ext
  intro k p r n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t f m
  change (uncurryRight (a y)).f n
    ((K ◁ leftAction A D N x y).f n
      ((α_ K (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (K ⊗ (x ⟶[Complex A] y)) (N.obj x) (k + p) r n hn
          (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl (t ⊗ₜ[A] f) ⊗ₜ[A] m)))) =
    (leftAction A D N' x y).f n
      (((x ⟶[Complex A] y) ◁ uncurryRight (a x)).f n
        ((α_ (x ⟶[Complex A] y) K (N.obj x)).hom.f n
          (((signedSwap K (x ⟶[Complex A] y)).hom ▷ N.obj x).f n
            (ιTensorObj (K ⊗ (x ⟶[Complex A] y)) (N.obj x) (k + p) r n hn
              (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl
                (t ⊗ₜ[A] f) ⊗ₜ[A] m)))))
  rw [associator_apply, whiskerLeft_apply, leftAction_apply, uncurryRight_apply,
    whiskerRight_apply, signedSwap_apply]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
  rw [associator_apply_of_sum, whiskerLeft_apply, uncurryRight_apply, leftAction_apply]
  change ((a y).f k t).v (p + r) n (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N f m (by omega)) =
    (k * p).negOnePow • SerrePositivity.DifferentialGraded.leftAction A N' f
      (((a x).f k t).v r (k + r) (by omega) m) (by omega)
  exact leftParamNaturality_apply_of_sum A a ha t f m (by omega) (by omega) (by omega)

end SerrePositivity.DifferentialGraded.BalancedTensor
