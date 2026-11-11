module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberRightShape
public import SerrePositivity.KST.LocalizingInvariants.StrictCoherentArrowPresentation

/-!
概要：fiber 正方形の第一枝の形状を、通常の cospan の元の左構造射の単体と同定する。
方針：ホーンの左辺をサイズ調整した nerve で読み、二対象と一つの射を計算する。
規約：形状の厳密な等号。使われ方：元の cospan の全自然変換への三角形表示の適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison

local instance rightCospanCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma rightShape_eq : rightShape.{u} =
    StrictArrow.shape.{u, u + 1} (AsSmall.up.map WalkingCospan.Hom.inl) := by
  apply SSet.yonedaEquiv.injective
  apply ULift.ext
  refine ComposableArrows.ext₁ rfl rfl ?_
  apply ULift.ext
  exact Subsingleton.elim _ _

lemma rightDiagram_eq {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) :
    rightShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (OmegaSpectrum.fromPoint Y)) =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge := by
  rw [rightShape, Category.assoc]
  exact CospanShape.strictDiagram_left _ _

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeComparison
