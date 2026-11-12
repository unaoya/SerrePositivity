module

public import SerrePositivity.KST.Spectra.SignedLoopSequence
public import SerrePositivity.KST.Spectra.SpectrumHomotopyRectification

/-!
概要：元の Ω スペクトルから符号を調整した loop の BF 模型への実際の射。
方針：随伴構造射の成分での構造可換性を単射構造射に沿って厳密化する。
規約：BF 置換の比較射へ持ち上げた厳密なスペクトルの射を構成する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の元の対象からの標準射の前段。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：符号を変えた一段先の Kan loop 列の BF 置換。
方針：実証済みの Ω 条件を cofibrant 置換へ渡す。
規約：Kan 円の構造射の後で次数 -1 の前合成を施す。
使われ方：BF 1978 §2。随伴構造射の実際の比較の標的。 -/
def signedLoopModel (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  (KanSequence.signedLoopTail X.toKanSequence).cofibrantOmegaSpectrum
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)

/-- 概要：符号を調整した BF loop 模型から実際の Kan loop 列への比較射。
方針：cofibrant 置換の標準比較射を使う。
規約：各段で全単射に RLP を持つ。
使われ方：BF 1978 §2、HTT A.3.3。標準射の比較の因子分解。 -/
def signedLoopProjection (X : OmegaSpectrum.{u}) :
    KanSequence.Hom (signedLoopModel X).toKanSequence
      (KanSequence.signedLoopTail X.toKanSequence) :=
  KanSequence.cofibrantOmegaProjection _ _

/-- 概要：元の Ω スペクトルから符号を調整した BF loop 模型への厳密な射。
方針：Kan 円への随伴構造射の成分の等式を厳密化し、cofibrant 比較射へ持ち上げる。
規約：群の同型から対象の射を推論せず、実際の充填を使う。
使われ方：Goerss–Jardine I §7、BF 1978 §2。有理化の元の対象からの単位写像の構成。 -/
def signedLoopUnit (X : OmegaSpectrum.{u}) : X ⟶ signedLoopModel X :=
  rectifyInto X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence)
    (KanSequence.kanAdjoint_signedLoopTail_comm X.toKanSequence_omega)

/-- 概要：符号を調整した loop 模型への射は各段で全基点 π_* 同型。
方針：持ち上げた随伴構造射の同型性を厳密化の保存性へ渡す。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7。有理化の前に必要な模型の比較の検査。 -/
theorem signedLoopUnit_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopUnit X).app n).right :=
  rectifyInto_levelwise X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence)
    (KanSequence.kanAdjoint_signedLoopTail_comm X.toKanSequence_omega)
    (KanSequence.kanAdjoint_piIsomorphism X.toKanSequence_omega) n

/-- 概要：符号を調整した loop 模型への射は全整数次数で π_* 同型。
方針：各段の全基点同型性を整数次数へ移す。
規約：Sp の同値との比較はまだ主張しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の元の対象と loop 模型の実際の比較。 -/
theorem signedLoopUnit_piIsomorphism (X : OmegaSpectrum.{u}) : PiIsomorphism (signedLoopUnit X) :=
  piIsomorphism_of_levelwise _ (signedLoopUnit_levelwise X)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
