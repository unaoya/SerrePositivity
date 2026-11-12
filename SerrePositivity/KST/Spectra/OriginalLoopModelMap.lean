module

public import SerrePositivity.KST.Spectra.SignedLoopComparison
public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInverse
public import SerrePositivity.KST.Spectra.RationalSpectrumModelMap

/-!
概要：元の Ω スペクトルから有理化に使う通常の loop 模型への実際の射。
方針：符号を調整した模型への随伴の比較に、通常の模型からの比較の厳密な逆方向の射を合成する。
規約：群の同型からスペクトルの射を推論せず、全ての段で実際の射を構成する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の元の対象を始域とする単位写像。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：元の Ω スペクトルから有理化の loop 模型への実際の厳密な射。
方針：符号を変えた模型への随伴の厳密化に、模型の比較の逆方向の BF 射を合成する。
規約：選択の自然性はこの定義だけから主張しない。
使われ方：BF 1978 §2、HA §1.4.2。telescope 有理化の単位写像の前段。 -/
def originalLoopModelMap (X : OmegaSpectrum.{u}) : X ⟶ rationalizationModel X :=
  signedLoopUnit X ≫ levelwiseInverse (signedLoopComparison X) (signedLoopComparison_levelwise X)

/-- 概要：元のスペクトルから loop 模型への比較は各段で全基点 π_* 同型。
方針：随伴の比較と逆方向の BF 比較の各段の同型性を合成する。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7。模型の群の表示を実際の射に沿って元の対象へ戻す。 -/
theorem originalLoopModelMap_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((originalLoopModelMap X).app n).right :=
  (signedLoopUnit_levelwise X n).comp
    (levelwiseInverse_levelwise (signedLoopComparison X) (signedLoopComparison_levelwise X) n)

/-- 概要：元のスペクトルと loop 模型の実際の比較は全整数次数で同型。
方針：各段の同型性を整数次数の任意段表示へ移す。
規約：coherent nerve の同値の主張は含まない。
使われ方：BF 1978 §2、HA §1.4.2。単位写像の π_* の計算の始域の比較。 -/
theorem originalLoopModelMap_piIsomorphism (X : OmegaSpectrum.{u}) :
    PiIsomorphism (originalLoopModelMap X) :=
  piIsomorphism_of_levelwise _ (originalLoopModelMap_levelwise X)

/-- 概要：実際の模型の比較射が与える整数次数群の同型。
方針：実証済みの全単射な群準同型から乗法同型を作る。
規約：順方向は originalLoopModelMap の誘導準同型そのもの。
使われ方：Goerss–Jardine I §7、HA §1.4.2。有理化の単位写像に適合する群の表示。 -/
def originalLoopModelEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup X j ≃* homotopyGroup (rationalizationModel X) j :=
  (originalLoopModelMap_piIsomorphism X).groupEquiv j

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
