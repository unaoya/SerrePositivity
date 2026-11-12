module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit
public import SerrePositivity.KST.Spectra.FixedPointLevels

/-!
概要：群作用の homotopy fixed points と余単体 BF 対象の homotopy totalization の実際の BF 対象。
方針：段ごとの点つき Kan end の Ω 列を構成し、単射置換を最後に一度施す。
規約：Sp の ∞ 極限性は含まない。有理 Shapiro の比較は別に証明する。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。L9e の実際のスペクトルの構成。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：群作用の homotopy fixed points の置換前の Kan Ω 列。
方針：群圏の作用図式を Kan 列へ忘れ、各段で点つき end を取る。
規約：群の有限性は対象の構成では不要。
使われ方：HA §1.4.2、BF 1978 §2。hG の cofibrant 置換前の模型。 -/
def homotopyFixedPointsKan {G : Type u} [Group G] (A : GroupAction.{u} G) : KanSequence.{u} :=
  KanSequence.homotopyLimit
    ((AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A) ⋙ OmegaSpectrum.forgetToKan)

/-- 概要：群作用の homotopy fixed points の実際の BF 対象。
方針：段ごとの Kan end の Ω 条件を移し、単射構造射へ置換する。
規約：通常の fixed points の厳密極限と区別する。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。有限群作用に対する hG の対象。 -/
def homotopyFixedPoints {G : Type u} [Group G] (A : GroupAction.{u} G) : OmegaSpectrum.{u} :=
  OmegaSpectrum.homotopyLimit (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A)

/-- 概要：hG の BF 対象から段ごとの Kan end への比較。
方針：Kan Ω 列の単射置換の比較射を使う。
規約：対象の構成に有限性を使わない。
使われ方：HA §1.4.2、BF 1978 §2。有理比較の π_* を各段へ移す射。 -/
def homotopyFixedPointsProjection {G : Type u} [Group G] (A : GroupAction.{u} G) :
    KanSequence.Hom (homotopyFixedPoints A).toKanSequence (homotopyFixedPointsKan A) :=
  KanSequence.homotopyLimitProjection
    ((AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A) ⋙ OmegaSpectrum.forgetToKan)
    (fun i ↦ ((AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A).obj i).toKanSequence_omega)

/-- 概要：hG の BF 比較射は各段で全基点 π_* 同型。
方針：単射置換の比較の同型性を使う。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。有理 Shapiro の各段での検査。 -/
theorem homotopyFixedPointsProjection_levelwise {G : Type u} [Group G]
    (A : GroupAction.{u} G) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((homotopyFixedPointsProjection A).app n).right :=
  KanSequence.replacementProjection_piIsomorphism (homotopyFixedPointsKan A) n

/-- 概要：余単体 BF 対象の homotopy totalization の実際の BF 対象。
方針：余単体図式の段ごとの Kan end と Ω 条件を単射置換する。
規約：通常の Reedy Tot との比較と Sp の ∞ 極限性はここでは主張しない。
使われ方：HA §1.4.2、BF 1978 §2。L9e の Tot の Kan 模型。 -/
def homotopyTotalization (X : CosimplicialObject OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  OmegaSpectrum.homotopyLimit (AsSmall.down ⋙ X)

end

end SerrePositivity.KST.Spectra
