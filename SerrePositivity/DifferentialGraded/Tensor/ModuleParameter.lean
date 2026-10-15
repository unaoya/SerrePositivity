module
public import SerrePositivity.DifferentialGraded.Tensor.Actions
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex

/-! # パラメータ複体と右加群のbalanced作用の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 右balanced作用ではパラメータを横切る二つのKoszul符号が消える。 -/
lemma rightAction_tensorModule (K : Complex A) (M : RightModule A D) (x y : D) :
    rightAction A D (tensorModule K M) x y =
      (α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom ≫ K ◁ rightAction A D M x y := by
  apply triple_ext
  intro k r p n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t m f
  change (rightAction A D (tensorModule K M) x y).f n
    (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
      (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)) =
    (K ◁ rightAction A D M x y).f n
      ((α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom.f n
        (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
          (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)))
  rw [rightAction_apply, tensorModule_action K M (op y) (op x) p k r (k + r)
    (r + p) n rfl rfl hn, associator_apply, whiskerLeft_apply, rightAction_apply]
  have ht : t ⊗ₜ[A] ((r * p).negOnePow • moduleAction A M f m rfl) =
      (r * p).negOnePow • (t ⊗ₜ[A] moduleAction A M f m rfl) :=
    map_zsmul (TensorProduct.mk A _ _ t) ((r * p).negOnePow : ℤ) _
  rw [ht]
  simp only [Units.smul_def, map_zsmul]
  change ((k + r) * p).negOnePow • ((p * k).negOnePow •
      ιTensorObj K (M.obj (op x)) k (r + p) n (by omega)
        (t ⊗ₜ[A] moduleAction A M f m rfl)) =
    (r * p).negOnePow • ιTensorObj K (M.obj (op x)) k (r + p) n (by omega)
      (t ⊗ₜ[A] moduleAction A M f m rfl)
  rw [smul_smul, ← Int.negOnePow_add]
  have hs : (k + r) * p + p * k = r * p + 2 * (p * k) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity.DifferentialGraded.BalancedTensor
