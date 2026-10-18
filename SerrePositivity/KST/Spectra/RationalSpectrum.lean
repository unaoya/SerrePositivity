module

public import SerrePositivity.KST.Spectra.RationalLoopTensor
public import SerrePositivity.KST.Spectra.SpectrumTail

/-!
概要：実際の telescope によるスペクトルの有理化対象と全整数次数の群の計算。
方針：円の Kan 置換からの cotensor の次数射の telescope を取り、tail で次数を補正する。
規約：∞ 圏の局所化の普遍性や群同型から得られない対象間の射は主張しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。K 理論の有理係数の整数次数群。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：有理 telescope の元の loop 模型の群を元のスペクトルの群へ戻す。
方針：円の anodyne な Kan 置換単位による比較と loop の次数移動を合成する。
規約：全整数次数 j。スペクトル間の射を群の同型から推論しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の次数と係数の補正。 -/
def rationalModelHomotopyEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (cotensor CirclePower.space.{u} X) (j - 1) ≃* homotopyGroup X j :=
  (PiIsomorphism.groupEquiv
    (cotensorPre_piIsomorphism_of_anodyne CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) X) (j - 1)).trans
        ((cotensorLoopHomotopyEquiv X (j - 1)).trans (by rw [sub_add_cancel]))

/-- 概要：実際の次数射の telescope から構成した有理化の BF 対象。
方針：loop の次数射の filtered Kan 余極限を cofibrant に置換し、零段を落とす。
規約：構成に使う射はすべて実際の厳密なスペクトルの射。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理係数のスペクトルの対象。 -/
def rationalization (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  tail (rationalLoopTelescope X)

/-- 概要：スペクトルの有理化対象の全整数次数の群は元の群の有理テンソル積。
方針：tail、telescope の群の余極限、円の Kan 置換と loop の群の同型を合成する。
規約：乗法表示の群を Additive に移して ℤ 上のテンソル積を取る。
使われ方：BF 1978 §2、HA §1.4.2。有理化の π_* 計算の主宣言。 -/
def rationalizationHomotopyEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (rationalization X) j ≃*
      Multiplicative (Additive (homotopyGroup X j) ⊗[ℤ] ℚ) :=
  (tailHomotopyEquiv (rationalLoopTelescope X) j).trans
    ((rationalLoopTensorEquiv X (j - 1)).trans
      (AddEquiv.toMultiplicative (TensorProduct.congr
        (MulEquiv.toAdditive (rationalModelHomotopyEquiv X j)).toIntLinearEquiv
          (LinearEquiv.refl ℤ ℚ)).toAddEquiv))

/-- 概要：有理化の全整数次数群と ℚ テンソルの同型の加法・線形表示。
方針：乗法同型を Additive と Multiplicative の標準比較で加法同型へ移す。
規約：ℤ 加群構造は加法群の標準構造を使う。
使われ方：BF 1978 §2、HA §1.4.2。加法的な K 理論の有理係数の計算。 -/
def rationalizationTensorEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    Additive (homotopyGroup (rationalization X) j) ≃ₗ[ℤ]
      Additive (homotopyGroup X j) ⊗[ℤ] ℚ :=
  ((MulEquiv.toAdditive (rationalizationHomotopyEquiv X j)).trans
    (AddEquiv.additiveMultiplicative _)).toIntLinearEquiv

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
