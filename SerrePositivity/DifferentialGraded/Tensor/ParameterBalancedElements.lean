module
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Tensor.Elements

/-! # パラメータ付きbalanced関係の斉次生成元公式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 左パラメータを固定したbalanced関係。パラメータの次数による余分な符号はない。 -/
lemma paramFamily_balanced_element {M : RightModule A D} {N : LeftModule A D}
    {K T : Complex A} (a : ParamFamily A D M N K T) (x y : D)
    {k r p s n : ℤ} (t : K.X k) (m : (M.obj (op y)).X r)
    (f : GradedHom A x y p) (v : (N.obj x).X s) (hn : k + (r + p + s) = n) :
    (r * p).negOnePow • (a.val x).f n
      (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + p + s) n hn
        (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) (r + p) s (r + p + s) rfl
          (moduleAction A M f m rfl ⊗ₜ[A] v))) =
    (a.val y).f n
      (ιTensorObj K (M.obj (op y) ⊗ N.obj y) k (r + p + s) n (by omega)
        (t ⊗ₜ[A] ιTensorObj (M.obj (op y)) (N.obj y) r (p + s) (r + p + s) (by omega)
          (m ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A N
            (n := p + s) f v (by omega)))) := by
  rcases a with ⟨a, ha⟩
  have h := congrArg (fun z => z.f n
    (ιTensorObj K ((M.obj (op y) ⊗ (x ⟶[Complex A] y)) ⊗ N.obj x)
      k (r + p + s) n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x)
        (r + p) s (r + p + s) rfl
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] v)))) (ha x y)
  simp only [comp_f, ModuleCat.comp_apply, whiskerLeft_comp] at h
  rw [whiskerLeft_apply, whiskerRight_apply, rightAction_apply,
    whiskerLeft_apply, associator_apply, whiskerLeft_apply, whiskerLeft_apply,
    leftAction_apply] at h
  have ht (z : (M.obj (op x) ⊗ N.obj x).X (r + p + s)) (i : ℤ) :
      t ⊗ₜ[A] (i • z) = i • (t ⊗ₜ[A] z) :=
    map_zsmul (TensorProduct.mk A _ _ t) i z
  simpa only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul, ht] using h

end SerrePositivity.DifferentialGraded.BalancedTensor
