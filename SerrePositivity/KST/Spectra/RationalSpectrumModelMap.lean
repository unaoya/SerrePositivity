module

public import SerrePositivity.KST.Spectra.RationalSpectrum
public import SerrePositivity.KST.Spectra.SpectrumTailNaturality

/-!
概要：次数補正した loop 模型から有理 telescope への実際の射と π_* の計算。
方針：telescope の零段の射を tail に送り、群の次数比較の自然性を使う。
規約：この模型と元の X の群の同型からスペクトル間の射は推論しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の標準射の構成の中間比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：有理化の次数を合わせた loop 模型。
方針：円の Kan 置換からの cotensor の零段を落とす。
規約：元と同じ整数次数群を持つことを別途証明する。
使われ方：BF 1978 §2、HA §1.4.2。telescope への実際の射の始域。 -/
def rationalizationModel (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  tail (cotensor CirclePower.space.{u} X)

/-- 概要：次数を合わせた loop 模型と元のスペクトルの整数次数群の同型。
方針：tail の次数比較と円の Kan 置換の比較を合成する。
規約：群の同型であり、対象間の射を含まない。
使われ方：BF 1978 §2、HA §1.4.2。標準射の π_* の式の始域の表示。 -/
def rationalizationModelHomotopyEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (rationalizationModel X) j ≃* homotopyGroup X j :=
  (tailHomotopyEquiv (cotensor CirclePower.space.{u} X) j).trans
    (rationalModelHomotopyEquiv X j)

/-- 概要：次数を合わせた loop 模型から有理 telescope への実際の厳密な射。
方針：filtered 余極限の零段の注入射を tail 関手へ送る。
規約：元の X を始域とする射とは区別する。
使われ方：BF 1978 §2、HA §1.4.2。有理化写像の構成の中間射。 -/
def rationalizationModelMap (X : OmegaSpectrum.{u}) :
    rationalizationModel X ⟶ rationalization X :=
  tailMap (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0))

/-- 概要：loop 模型から有理化への実際の射は整数次数群で a⊗1 を誘導する。
方針：tail の自然性、telescope の零段の式、テンソル積の同型の純テンソルの式を使う。
規約：始域の群を元の X の群へ同定した下で計算する。
使われ方：BF 1978 §2、HA §1.4.2。有理化の中間射の全整数次数の検証。 -/
theorem rationalizationModelMap_homotopy (X : OmegaSpectrum.{u}) (j : ℤ)
    (a : homotopyGroup (rationalizationModel X) j) :
    rationalizationHomotopyEquiv X j (homotopyMap (rationalizationModelMap X) j a) =
      Multiplicative.ofAdd
        (Additive.ofMul (rationalizationModelHomotopyEquiv X j a) ⊗ₜ[ℤ] (1 : ℚ)) := by
  simp only [rationalizationHomotopyEquiv, MulEquiv.trans_apply]
  erw [show tailHomotopyEquiv (rationalLoopTelescope X) j
      (homotopyMap (rationalizationModelMap X) j a) =
        homotopyMap (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0))
          (j - 1) (tailHomotopyEquiv (cotensor CirclePower.space.{u} X) j a) from
    tailHomotopyEquiv_natural _ _ _]
  erw [rationalLoopTensorEquiv_injection_zero]
  change Multiplicative.ofAdd
    ((TensorProduct.congr
      (MulEquiv.toAdditive (rationalModelHomotopyEquiv X j)).toIntLinearEquiv
        (LinearEquiv.refl ℤ ℚ))
      (Additive.ofMul (tailHomotopyEquiv (cotensor CirclePower.space.{u} X) j a) ⊗ₜ[ℤ]
        (1 : ℚ))) = _
  rw [TensorProduct.congr_tmul]
  rfl

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
