module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeAttachmentCoherence

/-!
概要：右枝の Hom 比較と付加辺面の比較を、同じ native な合成係数を終点に持つ円柱へ移す。
方針：同じ raw な円柱を保持し、初期 Hom の底の厳密な式で両端だけを表示変更する。
規約：元の枝と実際の付加辺を保持。使われ方：HL・HR の元の類を含む経路の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC)
  (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "qb" => sliceUnderProjection (j ≫ p)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "U" => coconePointHomFamily d y ≫ cosliceRestrictionFiberMap p j y
local notation "k" => SpecifiedCoconeBranchData.right (specifiedCoconeBranchData hp p c hc dB dC)
local notation "b" => coconeRestrictionEdgeApex j dC d k
local notation "N" => coconeApexHomPrecomposition dC d b y
local notation "leg" => colimitAttachmentHomPrecomposition c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC y
local notation "Φ" => colimitAttachmentTotalPrecomposition c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC y
local notation "IB" => specifiedCoconeRightBranchInitialHomFamily hp p c hc dB dC y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)
local notation "Pb" => leftFibrationInitialProjection qb dC y ≫
  Iso.hom (leftFibrationInitialBaseIso qb dC y)

/-- 枝の同じ比較円柱に付加辺を前合成し、元の HL・HR と連続する端点へ揃える。 -/
def specifiedCoconeRightBranchLegHomotopy : SSet.Homotopy
    (U ≫ coconeMappingSpaceHomComparison dC hC y ≫ leg) (N ≫ leg) :=
  homotopyEndpointTransport
    (functorHomotopyPostcomp (specifiedCoconeRightBranchHomotopy hp p c hc dB dC hC y) leg)
    (Category.assoc _ _ _) rfl

/-- 元の枝比較円柱の raw な付加辺前合成像を厳密に保持する。 -/
lemma specifiedCoconeRightBranchLegHomotopy_raw :
    (specifiedCoconeRightBranchLegHomotopy hp p c hc dB dC hC y).h =
      (specifiedCoconeRightBranchHomotopy hp p c hc dB dC hC y).h ≫ leg :=
  homotopyEndpointTransport_raw _ _ _

/-- 前置後の枝終点の初期 Hom の底は、同じ native な二脚の前合成である。 -/
lemma specifiedCoconeRightAttachmentInitialHomFamily_projection : (IB ≫ Φ) ≫ P = N ≫ leg := by
  calc
    _ = IB ≫ (Φ ≫ P) := Category.assoc _ _ _
    _ = IB ≫ (Pb ≫ leg) := congrArg (IB ≫ ·)
      (colimitAttachmentTotalPrecomposition_pinched c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC y)
    _ = (IB ≫ Pb) ≫ leg := (Category.assoc _ _ _).symm
    _ = N ≫ leg := congrArg (· ≫ leg)
      (specifiedCoconeRightBranchInitialHomFamily_projection hp p c hc dB dC y)

/-- 元の根辺初期族から native な二脚の係数へ至る、同じ付加辺面の比較円柱。 -/
def specifiedCoconeRightAttachmentHomotopy : SSet.Homotopy
    (specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫ P) (N ≫ leg) :=
  homotopyEndpointTransport
    (functorHomotopyPostcomp
      (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y) P) rfl
    (specifiedCoconeRightAttachmentInitialHomFamily_projection hp p c hc dB dC y)

/-- 表示変更後も、同じ付加辺面の初期 Hom 円柱の raw な底の射影である。 -/
lemma specifiedCoconeRightAttachmentHomotopy_raw :
    (specifiedCoconeRightAttachmentHomotopy hp p c hc dB dC y).h =
      (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h ≫ P :=
  homotopyEndpointTransport_raw _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
