module

public import SerrePositivity.KST.Spectra.RawRationalDiagram
public import SerrePositivity.KST.Spectra.RationalSpectrumUnit

/-!
概要：置換前の関手的な図式を介した有理化対象の実際の比較射。
方針：内部 Hom の厳密な図式の余極限を BF 置換し、既存の対象との各段 π_* 同型を構成する。
規約：関手法則と単位の自然性は後続で誘導群準同型について検証する。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理化の射の実現。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：内部 Hom の厳密な図式から得る BF telescope。
方針：Kan 図式の Ω 条件を使い、段の余極限を単射置換する。
規約：∞ 余極限の普遍性は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の比較対象。 -/
def rawRationalLoopTelescope (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  KanSequence.filteredOmegaSpectrum (rawRationalDiagram X) (rawRationalDiagram_omega X)

/-- 概要：スペクトルの射は内部 Hom の telescope 間の実際の BF 射を与える。
方針：厳密な図式の自然変換を余極限の比較射へ持ち上げる。
規約：選んだ持ち上げの厳密な関手法則を仮定しない。
使われ方：BF 1978 §2、HTT A.3.3。有理化の射の実現。 -/
def rawRationalLoopMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    rawRationalLoopTelescope X ⟶ rawRationalLoopTelescope Y :=
  KanSequence.filteredSpectrumMap (rawRationalDiagram_omega X) (rawRationalDiagram_omega Y)
    (rawRationalDiagramMap f)

/-- 概要：既存の有理 telescope から内部 Hom の telescope への実際の比較。
方針：cotensor の射影の自然変換を BF 比較へ持ち上げる。
規約：始域は既存の有理化に使う telescope そのもの。
使われ方：BF 1978 §2、HA §1.4.2。既存の群のテンソル表示を保つ。 -/
def rationalLoopProjection (X : OmegaSpectrum.{u}) :
    rationalLoopTelescope X ⟶ rawRationalLoopTelescope X :=
  KanSequence.filteredSpectrumMap (D := rationalDiagram X ⋙ forgetToKan)
    (fun a ↦ ((rationalDiagram X).obj a).toKanSequence_omega)
    (rawRationalDiagram_omega X) (rationalDiagramProjection X)

/-- 概要：有理 telescope の比較射は全ての段で全基点 π_* 同型。
方針：filtered 比較射の成分の同型性の保存を使う。
規約：零次数を含む。
使われ方：BF 1978 §2、Goerss–Jardine I §7。逆方向の実際の射の構成条件。 -/
theorem rationalLoopProjection_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((rationalLoopProjection X).app n).right :=
  KanSequence.filteredSpectrumMap_levelwise
    (D := rationalDiagram X ⋙ forgetToKan) (E := rawRationalDiagram X)
    (fun a ↦ ((rationalDiagram X).obj a).toKanSequence_omega)
    (rawRationalDiagram_omega X) (rationalDiagramProjection X)
    (rationalDiagramProjection_levelwise X) n

/-- 概要：次数移動した有理化対象を関手的な図式の BF 対象へ比較する。
方針：telescope の比較射を一段移す。
規約：始域は既存の有理化対象。
使われ方：BF 1978 §2、HA §1.4.2。有理化の実際の射の始域と終域。 -/
def rationalizationProjection (X : OmegaSpectrum.{u}) :
    rationalization X ⟶ tail (rawRationalLoopTelescope X) :=
  tailMap (rationalLoopProjection X)

/-- 概要：有理化対象の比較は各段で全基点 π_* 同型。
方針：telescope の比較の同型性を一段ずらす。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7。比較射の逆方向への BF 射。 -/
theorem rationalizationProjection_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((rationalizationProjection X).app n).right :=
  rationalLoopProjection_levelwise X (n + 1)

/-- 概要：元の射から有理化対象間の実際の厳密な射を構成する。
方針：関手的な図式の BF 比較を通り、標的の比較の逆方向の射で既存の対象へ戻す。
規約：単位の自然性と関手法則は後続で π_* 上で検証する。
使われ方：BF 1978 §2、HA §1.4.2。有理化の射への作用。 -/
def rationalizationMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    rationalization X ⟶ rationalization Y :=
  rationalizationProjection X ≫ tailMap (rawRationalLoopMap f) ≫
    levelwiseInverse (rationalizationProjection Y) (rationalizationProjection_levelwise Y)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
