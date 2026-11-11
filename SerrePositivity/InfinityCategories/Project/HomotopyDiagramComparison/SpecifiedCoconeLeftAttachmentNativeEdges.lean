module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeAttachmentCoherence

/-!
概要：左枝の Hom 比較と付加辺面の比較を、同じ native な合成係数を終点に持つ円柱へ移す。
方針：同じ raw な円柱を保持し、初期 Hom の底の厳密な式で両端だけを表示変更する。
規約：元の枝と実際の付加辺を保持。使われ方：HL・HR の元の類を含む経路の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
  (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "qb" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "U" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTransportEdge hp p c hc dB dC
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRestrictionEdgeApex i dB d k
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeApexHomPrecomposition dB d b y
local notation "leg" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y
local notation "Φ" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition c hc f (i ≫ p) rfl dB y
local notation "IB" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
  Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y)
local notation "Pb" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection qb dB y ≫
  Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso qb dB y)

/-- 枝の同じ比較円柱に付加辺を前合成し、元の HL・HR と連続する端点へ揃える。 -/
def specifiedCoconeLeftBranchLegHomotopy : SSet.Homotopy
    (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison dB hB y ≫ leg) (N ≫ leg) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchHomotopy hp p c hc dB hB dC y) leg)
    (Category.assoc _ _ _) rfl

/-- 元の枝比較円柱の raw な付加辺前合成像を厳密に保持する。 -/
lemma specifiedCoconeLeftBranchLegHomotopy_raw :
    (specifiedCoconeLeftBranchLegHomotopy hp p c hc dB hB dC y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchHomotopy hp p c hc dB hB dC y).h ≫ leg :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 前置後の枝終点の初期 Hom の底は、同じ native な二脚の前合成である。 -/
lemma specifiedCoconeLeftAttachmentInitialHomFamily_projection : (IB ≫ Φ) ≫ P = N ≫ leg := by
  calc
    _ = IB ≫ (Φ ≫ P) := Category.assoc _ _ _
    _ = IB ≫ (Pb ≫ leg) := congrArg (IB ≫ ·)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition_pinched c hc f (i ≫ p) rfl dB y)
    _ = (IB ≫ Pb) ≫ leg := (Category.assoc _ _ _).symm
    _ = N ≫ leg := congrArg (· ≫ leg)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchInitialHomFamily_projection hp p c hc dB dC y)

/-- 元の根辺初期族から native な二脚の係数へ至る、同じ付加辺面の比較円柱。 -/
def specifiedCoconeLeftAttachmentHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫ P) (N ≫ leg) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y) P) rfl
    (specifiedCoconeLeftAttachmentInitialHomFamily_projection hp p c hc dB dC y)

/-- 表示変更後も、同じ付加辺面の初期 Hom 円柱の raw な底の射影である。 -/
lemma specifiedCoconeLeftAttachmentHomotopy_raw :
    (specifiedCoconeLeftAttachmentHomotopy hp p c hc dB dC y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h ≫ P :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
