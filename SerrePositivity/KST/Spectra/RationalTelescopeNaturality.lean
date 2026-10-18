module

public import SerrePositivity.KST.Spectra.RationalGroupTelescope

/-!
概要：乗法列の直極限と ℚ テンソルの比較の自然性。
方針：加法準同型を各段へ施し、局所化の普遍性で標準射上の計算から比較する。
規約：全ての加法群は可換。元の群にねじれがあってもよい。
使われ方：BF 1978 §2、HA §1.4.2。L9d の π_* の有理化の自然性。
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.RationalTelescope

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- 概要：加法準同型は乗法列の線形遷移と可換。
方針：加法準同型の標準 ℤ 線形化のスカラー保存を使う。
規約：全ての二段間の遷移に適用する。
使われ方：HA §1.4.2。直極限の誘導写像の入力。 -/
theorem scalarTransition_compatible (f : A →+ B) (i j : ℕ) (hij : i ≤ j) :
    f.toIntLinearMap.comp (scalarTransition A i j hij) =
      (scalarTransition B i j hij).comp f.toIntLinearMap := by
  ext a
  exact f.toIntLinearMap.map_smul (integerCoefficient i j) a

/-- 概要：加法準同型が乗法列の直極限に誘導する標準線形写像。
方針：加群の直極限の射を作り、標準の ℤ 加群構造で線形化する。
規約：各段で同じ f を使う。
使われ方：HA §1.4.2。有理化の群の関手性。 -/
def limitMap (f : A →+ B) : additiveLimit A →ₗ[ℤ] additiveLimit B :=
  (Module.DirectLimit.map (fun _ : ℕ ↦ f.toIntLinearMap)
    (scalarTransition_compatible f)).toAddMonoidHom.toIntLinearMap

/-- 概要：直極限の誘導写像は各段で元の準同型を適用する。
方針：直極限の map の代表における計算則を使う。
規約：任意の段 i。
使われ方：HA §1.4.2。有理化比較の自然性の計算。 -/
@[simp]
theorem limitMap_inclusion (f : A →+ B) (i : ℕ) (a : A) :
    limitMap f (inclusion A i a) = inclusion B i (f a) :=
  Module.DirectLimit.map_apply_of (fun _ : ℕ ↦ f.toIntLinearMap) (scalarTransition_compatible f) a

/-- 概要：直極限の誘導写像は恒等準同型を保つ。
方針：任意の元を一段の代表として計算する。
規約：標準の ℤ 線形写像の等式。
使われ方：HA §1.4.2。有理化の群の関手の恒等法則。 -/
@[simp]
theorem limitMap_id : limitMap (AddMonoidHom.id A) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  obtain ⟨i, a, rfl⟩ := exists_inclusion A y
  rw [limitMap_inclusion]
  rfl

/-- 概要：直極限の誘導写像は準同型の合成を保つ。
方針：各段の代表で二回の誘導写像を計算する。
規約：合成の順は g∘f。
使われ方：HA §1.4.2。有理化の群の関手の合成法則。 -/
theorem limitMap_comp (f : A →+ B) (g : B →+ C) :
    limitMap (g.comp f) = (limitMap g).comp (limitMap f) := by
  apply LinearMap.ext
  intro y
  obtain ⟨i, a, rfl⟩ := exists_inclusion A y
  simp only [LinearMap.comp_apply, limitMap_inclusion, AddMonoidHom.comp_apply]

/-- 概要：乗法列の直極限と ℚ テンソルの比較同型は加法準同型に関して自然。
方針：局所化の標準射の後で比較し、a⊗1 の計算を使う。
規約：ℤ 線形写像の可換式として述べる。
使われ方：BF 1978 §2、HA §1.4.2。有理化の π_* 比較の自然性。 -/
theorem additiveLimitTensorEquiv_natural (f : A →+ B) :
    (additiveLimitTensorEquiv B).toLinearMap.comp (limitMap f) =
      (TensorProduct.map f.toIntLinearMap (LinearMap.id : ℚ →ₗ[ℤ] ℚ)).comp
        (additiveLimitTensorEquiv A).toLinearMap := by
  apply IsLocalizedModule.ext (nonZeroDivisors ℤ) (inclusion A 0)
    (IsLocalizedModule.map_units (rationalTensorUnit B))
  ext a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, limitMap_inclusion,
    additiveLimitTensorEquiv_zero, TensorProduct.map_tmul]
  rfl

end

end SerrePositivity.KST.Spectra.RationalTelescope
