module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Module.Rat

/-!
概要：有理テンソル積を始域とする加法準同型は a⊗1 の像で決まる。
方針：ℚ を左へ交換し、加法準同型の有理数倍の保存とテンソル積の生成元での帰納法を使う。
規約：加法群には標準の ℤ 加群構造を使う。
使われ方：HA §1.4.2、BF 1978 §2。有理化のテンソル表示の自然性と関手法則。
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace SerrePositivity.KST.Spectra

/-- 概要：左側の有理テンソル積の加法準同型は 1⊗a の像で決まる。
方針：任意の純テンソルは 1⊗a の有理数倍である。
規約：追加の ℚ 線形性を仮定しない。
使われ方：HA §1.4.2。有理化の群準同型の一意性。 -/
theorem rationalLeftTensor_addHom_ext {G : Type u} {H : Type v}
    [AddCommGroup G] [AddCommGroup H]
    (f g : (ℚ ⊗[ℤ] G) →+ (ℚ ⊗[ℤ] H))
    (h : ∀ a, f ((1 : ℚ) ⊗ₜ[ℤ] a) = g ((1 : ℚ) ⊗ₜ[ℤ] a)) : f = g := by
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q a =>
    have he : q ⊗ₜ[ℤ] a = q • ((1 : ℚ) ⊗ₜ[ℤ] a) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_rat_smul, map_rat_smul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 概要：右側の有理テンソル積の加法準同型は a⊗1 の像で決まる。
方針：テンソル因子を交換し、左側の有理テンソル積の一意性へ還元する。
規約：ℤ 線形性以外の条件を追加しない。
使われ方：HA §1.4.2、BF 1978 §2。有理化の実際の射の誘導準同型を同定する。 -/
theorem rationalTensor_addHom_ext {G : Type u} {H : Type v}
    [AddCommGroup G] [AddCommGroup H]
    (f g : (G ⊗[ℤ] ℚ) →+ (H ⊗[ℤ] ℚ))
    (h : ∀ a, f (a ⊗ₜ[ℤ] (1 : ℚ)) = g (a ⊗ₜ[ℤ] (1 : ℚ))) : f = g := by
  let eG := (TensorProduct.comm ℤ ℚ G).toAddEquiv
  let eH := (TensorProduct.comm ℤ ℚ H).toAddEquiv
  have hc : eH.symm.toAddMonoidHom.comp (f.comp eG.toAddMonoidHom) =
      eH.symm.toAddMonoidHom.comp (g.comp eG.toAddMonoidHom) := by
    apply rationalLeftTensor_addHom_ext
    intro a
    simp only [AddMonoidHom.comp_apply, LinearEquiv.coe_toAddEquiv,
      eG]
    exact congrArg eH.symm (h a)
  apply AddMonoidHom.ext
  intro x
  apply eH.symm.injective
  have hx := DFunLike.congr_fun hc (eG.symm x)
  change eH.symm (f (eG (eG.symm x))) = eH.symm (g (eG (eG.symm x))) at hx
  simpa only [AddEquiv.apply_symm_apply] using hx

end SerrePositivity.KST.Spectra
