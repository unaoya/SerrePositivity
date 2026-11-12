module

public import SerrePositivity.KST.LocalizingInvariants.BFFiberInfinityCone
public import SerrePositivity.KST.LocalizingInvariants.SpectrumConeLeg
public import SerrePositivity.KST.LocalizingInvariants.ConeEdgeLeg

/-!
概要：置換済み fiber の錐の脚と、長完全列の包含の射の類の一致。
方針：slice 内の比較辺の三角形に脚を制限し、元の厳密な包含の合成式を使う。
規約：元の BF 射の Sp における射の類を比較する。使われ方：K-5 の包含の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance fiberLegSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ n, Fibration (p.app n).right]

/-- 実 fiber の錐の元の脚を BF 射として回収する。 -/
def rawLeg (i : AsSmall.{u} WalkingCospan) : obj p hp ⟶
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y)).obj i :=
  SpectrumConeLeg.map (infinityCone p) (infinityCone_vertex p) i

/-- 置換済み fiber の錐の脚を BF 射として回収する。 -/
def replacedLeg (i : AsSmall.{u} WalkingCospan) : fiber p hp ⟶
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y)).obj i :=
  SpectrumConeLeg.map (replacedCone p) (replacedCone_vertex p) i

lemma rawLeg_left : rawLeg p (AsSmall.up.obj WalkingCospan.left) = inclusion p hp :=
  SpectrumConeLeg.map_strict (i := AsSmall.up.obj WalkingCospan.left) (b := smallCone p)

/-- 回収した各脚は、元の比較射を含む同じ合成三角形を満たす。 -/
lemma comparison_legs (i : AsSmall.{u} WalkingCospan) :
    SpectrumHo.hom (comparison p hp) ≫ SpectrumHo.hom (rawLeg p i) =
      SpectrumHo.hom (replacedLeg p i) := by
  let a := replacedConeComparison p
  let k := ULift.up (ComposableArrows.mk₀ i)
  exact ConeEdgeLeg.homMk_comp_transport
    (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (infinityCone p) k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (replacedCone p) k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (comparison p hp)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (rawLeg p i)).toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (replacedLeg p i)).toTruncated
    (ConeEdgeLeg.homMk_naturality a k)
    (replacedCone_vertex p) (infinityCone_vertex p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y)) i)
    (replacedConeComparison_projection p)
    (SpectrumConeLeg.map_edge _ _ i).symm (SpectrumConeLeg.map_edge _ _ i).symm

/-- 置換後の図式上では、fiber への脚の類は元の包含の類そのもの。 -/
lemma replacedLeg_left_hom :
    SpectrumHo.hom (replacedLeg p (AsSmall.up.obj WalkingCospan.left)) =
      SpectrumHo.hom (fiberInclusion p hp) := by
  have h := comparison_legs p (AsSmall.up.obj WalkingCospan.left)
  rw [rawLeg_left, ← SpectrumHo.hom_comp, comparison_inclusion] at h
  exact h.symm

end SerrePositivity.KST.LocalizingInvariants.FiberModel
