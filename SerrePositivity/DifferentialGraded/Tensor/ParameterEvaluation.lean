module
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Tensor.RightParameter
public import SerrePositivity.DifferentialGraded.Tensor.Elements

/-! # 左右パラメータ付き降下の純粋生成元計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

lemma paramDesc_element {K T : Complex A} (a : ParamFamily A D M N K T) (x : D)
    {k r s l n : ℤ} (hl : r + s = l) (hn : k + l = n)
    (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) :
    (paramDesc A D M N a).f n
      (ιTensorObj K (obj A D M N) k l n hn (t ⊗ₜ[A] element A D M N x m v hl)) =
    (a.val x).f n (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v))) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v))))
    (ι_paramDesc A D M N a x)
  change (paramDesc A D M N a).f n ((K ◁ ι A D M N x).f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v)))) = _ at h
  rw [whiskerLeft_apply] at h
  exact h

lemma rightParamDesc_element {K T : Complex A} (a : RightParamFamily A D M N K T) (x : D)
    {r s l k n : ℤ} (hl : r + s = l) (hn : l + k = n)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (t : K.X k) :
    (rightParamDesc A D M N a).f n
      (ιTensorObj (obj A D M N) K l k n hn (element A D M N x m v hl ⊗ₜ[A] t)) =
    (a.val x).f n (ιTensorObj (M.obj (op x) ⊗ N.obj x) K l k n hn
      (ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v) ⊗ₜ[A] t)) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj (M.obj (op x) ⊗ N.obj x) K l k n hn
      (ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v) ⊗ₜ[A] t)))
    (ι_rightParamDesc A D M N a x)
  change (rightParamDesc A D M N a).f n ((ι A D M N x ▷ K).f n
    (ιTensorObj (M.obj (op x) ⊗ N.obj x) K l k n hn
      (ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v) ⊗ₜ[A] t))) = _ at h
  rw [whiskerRight_apply] at h
  exact h

lemma paramDesc_curry_element {K T : Complex A} (a : ParamFamily A D M N K T) (x : D)
    {k r s l n : ℤ} (hl : r + s = l) (hn : l + k = n)
    (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) :
    ((curryRight (paramDesc A D M N a)).f k t).v l n hn (element A D M N x m v hl) =
    (a.val x).f n (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n (by omega)
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v))) := by
  exact paramDesc_element A D M N a x hl (by omega) t m v

end SerrePositivity.DifferentialGraded.BalancedTensor
