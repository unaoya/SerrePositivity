module

public import SerrePositivity.KST.Spectra.RationalModuleTelescope
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing

/-!
概要：乗法列のアーベル群の直極限と ℚ テンソルとの線形同型。
方針：直極限の標準射が非零整数による加群の局所化であることを証明する。
規約：元の群にねじれがある場合も含む。スペクトルの有理化対象の構成とは別の群の計算。
使われ方：BF 1978 §2、HA §1.4.2。L9d の π_*(X_ℚ) の計算先。
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.RationalTelescope

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type u) [AddCommGroup A]

/-- 概要：乗法列の零段からの標準射は非零整数による加群の局所化。
方針：整数作用の可逆性、代表の分母表示、等式の後続段での検出を証明する。
規約：局所化を追加の入力にせず、三つの特徴条件を実証する。
使われ方：HA §1.4.2。乗法列の直極限と ℚ テンソルの比較。 -/
instance additiveLimit_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) (inclusion A 0) where
  map_units s := by
    apply (Module.End.isUnit_iff _).2
    change Function.Bijective (fun y : additiveLimit A ↦ (s : ℤ) • y)
    exact additiveLimit_smul_bijective A s (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  surj y := by
    obtain ⟨i, a, rfl⟩ := exists_inclusion A y
    refine ⟨⟨a, ⟨integerCoefficient 0 i, ?_⟩⟩, ?_⟩
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr (integerCoefficient_ne_zero 0 i)
    · change integerCoefficient 0 i • inclusion A i a = inclusion A 0 a
      rw [← (inclusion A i).map_smul (integerCoefficient 0 i) a]
      exact inclusion_transition A (Nat.zero_le i) a
  exists_of_eq h := by
    obtain ⟨j, _, hj⟩ := inclusion_eq_eventually A 0 _ _ h
    exact ⟨⟨integerCoefficient 0 j,
      mem_nonZeroDivisors_iff_ne_zero.mpr (integerCoefficient_ne_zero 0 j)⟩, hj⟩

/-- 概要：アーベル群から ℚ テンソルへの標準線形写像。
方針：一を左因子とするテンソルの射に交換同型を合成する。
規約：値は a⊗1、テンソルの順は A⊗ℚ。
使われ方：HA §1.4.2。有理化の標準写像の群での模型。 -/
def rationalTensorUnit : A →ₗ[ℤ] A ⊗[ℤ] ℚ :=
  (TensorProduct.comm ℤ ℚ A).toLinearMap.comp (TensorProduct.mk ℤ ℚ A 1)

/-- 概要：テンソルの標準射は a を a⊗1 に送る。
方針：テンソルの交換同型を単純テンソルで計算する。
規約：ℤ 上のテンソル積。
使われ方：HA §1.4.2。直極限比較の零段での計算。 -/
@[simp]
theorem rationalTensorUnit_apply (a : A) : rationalTensorUnit A a = a ⊗ₜ[ℤ] (1 : ℚ) := by
  simp [rationalTensorUnit]

/-- 概要：ℚ テンソルへの標準写像も非零整数による局所化。
方針：ℚ が ℤ の分数体であることと、テンソルによる加群の局所化の実構成を使う。
規約：交換同型によりテンソルの順を A⊗ℚ にそろえる。
使われ方：HA §1.4.2。乗法列の直極限との標準比較。 -/
instance rationalTensorUnit_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) (rationalTensorUnit A) := by
  change IsLocalizedModule (nonZeroDivisors ℤ)
    ((TensorProduct.comm ℤ ℚ A).toLinearMap ∘ₗ TensorProduct.mk ℤ ℚ A 1)
  infer_instance

/-- 概要：乗法列 2,3,4,… のアーベル群の直極限は A⊗ℚ と線形同型。
方針：二つの実証済みの局所化の普遍性を比較する。
規約：定義に ℚ テンソルとの同型を仮定していない。
使われ方：BF 1978 §2、HA §1.4.2。L9d の telescope の群の計算。 -/
def additiveLimitTensorEquiv : additiveLimit A ≃ₗ[ℤ] A ⊗[ℤ] ℚ :=
  IsLocalizedModule.linearEquiv (nonZeroDivisors ℤ) (inclusion A 0) (rationalTensorUnit A)

/-- 概要：直極限と ℚ テンソルの比較は零段の元を a⊗1 に送る。
方針：局所化比較同型の標準射における計算式を使う。
規約：任意のアーベル群 A。
使われ方：HA §1.4.2。有理化写像の π_* の同定。 -/
@[simp]
theorem additiveLimitTensorEquiv_zero (a : A) :
    additiveLimitTensorEquiv A (inclusion A 0 a) = a ⊗ₜ[ℤ] (1 : ℚ) := by
  simp [additiveLimitTensorEquiv]

end

end SerrePositivity.KST.Spectra.RationalTelescope
