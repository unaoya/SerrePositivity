module

public import SerrePositivity.KST.Spectra.OriginalLoopModelMap

/-!
概要：元のスペクトルから telescope 有理化への実際の単位写像と全次数のテンソル公式。
方針：loop 模型への実際の比較を telescope の零段の射へ合成し、比較に適合する群の表示を取る。
規約：群の同型だけから対象の射を推論しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の単位で a を a⊗1 へ送る公式。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：元の Ω スペクトルから有理 telescope への実際の厳密な単位写像。
方針：元の対象から loop 模型への比較と telescope の零段からの射を合成する。
規約：telescope の対象は既に構成した rationalization を使う。
使われ方：BF 1978 §2、HA §1.4.2。有理化の元の対象を始域とする写像。 -/
def rationalizationUnit (X : OmegaSpectrum.{u}) : X ⟶ rationalization X :=
  originalLoopModelMap X ≫ rationalizationModelMap X

/-- 概要：実際の模型の比較と既存の群の表示の差を表す自己同型。
方針：実際の比較射の誘導同型に従来の loop 模型の群の表示を合成する。
規約：追加の代数的仮定を含まない。
使われ方：HA §1.4.2。単位写像に適合するテンソル公式へ表示を合わせる。 -/
def rationalizationUnitCoefficientEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup X j ≃* homotopyGroup X j :=
  (originalLoopModelEquiv X j).trans (rationalizationModelHomotopyEquiv X j)

/-- 概要：単位写像の全次数群への作用を既存の群の表示で計算する。
方針：合成の関手性と loop 模型からの零段の注入の公式を使う。
規約：模型の実際の比較による自己同型を明示する。
使われ方：Goerss–Jardine I §7、HA §1.4.2。単位に適合する表示への補正前の公式。 -/
theorem rationalizationUnit_homotopy_coefficient (X : OmegaSpectrum.{u}) (j : ℤ)
    (a : homotopyGroup X j) :
    rationalizationHomotopyEquiv X j (homotopyMap (rationalizationUnit X) j a) =
      Multiplicative.ofAdd
        (Additive.ofMul (rationalizationUnitCoefficientEquiv X j a) ⊗ₜ[ℤ] (1 : ℚ)) := by
  change rationalizationHomotopyEquiv X j
    (homotopyMap (originalLoopModelMap X ≫ rationalizationModelMap X) j a) = _
  rw [homotopyMap_comp, MonoidHom.comp_apply, rationalizationModelMap_homotopy]
  rfl

/-- 概要：単位写像に適合する全整数次数の有理化群のテンソル表示。
方針：模型の比較による自己同型の逆を ℚ テンソルへ送り、既存のテンソル同型へ合成する。
規約：表示の選択を実際の単位写像に合わせる。
使われ方：BF 1978 §2、HA §1.4.2。元の群の元 a が a⊗1 へ写る公式。 -/
def rationalizationUnitHomotopyEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (rationalization X) j ≃*
      Multiplicative (Additive (homotopyGroup X j) ⊗[ℤ] ℚ) :=
  (rationalizationHomotopyEquiv X j).trans
    (AddEquiv.toMultiplicative (TensorProduct.congr
      (MulEquiv.toAdditive (rationalizationUnitCoefficientEquiv X j).symm).toIntLinearEquiv
        (LinearEquiv.refl ℤ ℚ)).toAddEquiv)

/-- 概要：群の自己同型の逆のテンソルは純テンソル上で元の自己同型を打ち消す。
方針：テンソルの同型の純テンソルでの式と群同型の往復を使う。
規約：群は可換、ℤ 加群構造は標準のもの。
使われ方：HA §1.4.2。大きなスペクトルの比較を展開せずに単位の係数を補正する。 -/
theorem unitTensorCoefficient_correction {G : Type u} [CommGroup G]
    (e : G ≃* G) (a : G) :
    (TensorProduct.congr (MulEquiv.toAdditive e.symm).toIntLinearEquiv
      (LinearEquiv.refl ℤ ℚ)) (Additive.ofMul (e a) ⊗ₜ[ℤ] (1 : ℚ)) =
        Additive.ofMul a ⊗ₜ[ℤ] (1 : ℚ) := by
  rw [TensorProduct.congr_tmul]
  change Additive.ofMul (e.symm (e a)) ⊗ₜ[ℤ] (1 : ℚ) = _
  rw [MulEquiv.symm_apply_apply]

/-- 概要：実際の有理化の単位写像は全整数次数で a を a⊗1 へ送る。
方針：係数の自己同型をその逆のテンソルで打ち消す。
規約：順写像は rationalizationUnit の実際の誘導準同型。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。K 理論の有理化の標準の群の公式。 -/
theorem rationalizationUnit_homotopy (X : OmegaSpectrum.{u}) (j : ℤ)
    (a : homotopyGroup X j) :
    rationalizationUnitHomotopyEquiv X j (homotopyMap (rationalizationUnit X) j a) =
      Multiplicative.ofAdd (Additive.ofMul a ⊗ₜ[ℤ] (1 : ℚ)) := by
  rw [rationalizationUnitHomotopyEquiv, MulEquiv.trans_apply,
    rationalizationUnit_homotopy_coefficient]
  change Multiplicative.ofAdd ((TensorProduct.congr
    (MulEquiv.toAdditive (rationalizationUnitCoefficientEquiv X j).symm).toIntLinearEquiv
      (LinearEquiv.refl ℤ ℚ))
        (Additive.ofMul (rationalizationUnitCoefficientEquiv X j a) ⊗ₜ[ℤ] (1 : ℚ))) = _
  exact congrArg Multiplicative.ofAdd
    (unitTensorCoefficient_correction (rationalizationUnitCoefficientEquiv X j) a)

/-- 概要：単位に適合する有理化の全整数次数の群の加法・線形表示。
方針：乗法同型を標準の加法同型へ移す。
規約：ℤ 加群構造は加法群の標準の構造。
使われ方：HA §1.4.2。有理係数の K 群を通常の加法群として使う。 -/
def rationalizationUnitTensorEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    Additive (homotopyGroup (rationalization X) j) ≃ₗ[ℤ]
      Additive (homotopyGroup X j) ⊗[ℤ] ℚ :=
  ((MulEquiv.toAdditive (rationalizationUnitHomotopyEquiv X j)).trans
    (AddEquiv.additiveMultiplicative _)).toIntLinearEquiv

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
