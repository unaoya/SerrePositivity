module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberLeg
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare
public import SerrePositivity.KST.LocalizingInvariants.ConeSquareLeg

/-!
概要：元の BF fiber 四角形の下辺と元の包含の照合。
方針：形状同型と錐の脚の制限を計算し、指定単位の比較を使う。
規約：下辺の一次単体と元の BF 射の類を区別する。使われ方：K-5 の長完全列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance fiberSquareLegSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma hornLeftVertex :
    CospanShape.strictCospanHornIso.{u, u + 1}.inv.app (Opposite.op ⦋0⦌)
      ConeSquareLeg.leftVertex =
    ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)) := by
  apply ULift.ext
  apply ComposableArrows.ext₀
  rfl

variable {E B : OmegaSpectrum.{u}} (f : E ⟶ B)

/-- 実 fiber 四角形の下辺は元の錐から回収した左脚の一単体。 -/
lemma homotopyFiberSquare_bottom_edge :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (homotopyFiberSquare f).square) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (homotopyFiberLeg f (AsSmall.up.obj WalkingCospan.left))).edge := by
  have hb := ConeSquareLeg.bottom (hornCone f)
  have hr := ConeSquareLeg.leg_restrict (homotopyFiberCone f)
    CospanShape.strictCospanHornIso.inv ConeSquareLeg.leftVertex
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion ConeSquareLeg.leftVertex ≫ (hornCone f).val = _ at hr
  rw [hornLeftVertex] at hr
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (hornCone f)) = _
  rw [hb, hr]
  exact (SSet.yonedaEquiv_comp _ _).trans (SpectrumConeLeg.map_edge _ _ _).symm

/-- 下辺を元の BF 端点で表示した辺。 -/
def homotopyFiberSquareBottom : Sp.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyFiber f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex E) where
  edge := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (homotopyFiberSquare f).square)
  src_eq := by
    rw [homotopyFiberSquare_bottom_edge]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (homotopyFiberLeg f (AsSmall.up.obj WalkingCospan.left))).src_eq
  tgt_eq := by
    rw [homotopyFiberSquare_bottom_edge]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (homotopyFiberLeg f (AsSmall.up.obj WalkingCospan.left))).tgt_eq

/-- 下辺は、元の homotopyFiberInclusion のホモトピー圏での射そのもの。 -/
lemma homotopyFiberSquare_bottom_hom :
    SSet.Truncated.HomotopyCategory.homMk (homotopyFiberSquareBottom f).toTruncated =
      SpectrumHo.hom (homotopyFiberInclusion f) := by
  have he : homotopyFiberSquareBottom f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (homotopyFiberLeg f (AsSmall.up.obj WalkingCospan.left)) :=
    SSet.Edge.ext (homotopyFiberSquare_bottom_edge f)
  exact (congrArg (fun e ↦ SSet.Truncated.HomotopyCategory.homMk
    (SSet.Edge.toTruncated e)) he).trans (homotopyFiberLeg_left_hom f)

end SerrePositivity.KST.LocalizingInvariants.FiberModel
