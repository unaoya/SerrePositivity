module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftAttachmentNativeEdges
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightAttachmentNativeEdges

/-!
概要：元の HL・HR と枝 Hom 比較の合成を、元の根辺円柱と付加辺面円柱の合成へ同定する。
方針：実際の四円柱の raw な射影と同じ類の回収を、既存の合成等式へ代入する。
規約：元の辺の類を保持。使われ方：native な二単体経路との合成と共通 end の貼り合わせ。
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
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)

section
local notation "H₀" => specifiedCoconeLeftUniversalInitialHomotopy hp p c hc dB hB dC y
local notation "H₁" => specifiedCoconeLeftBranchToInitialHomotopy hp p c hc dB hB dC y
local notation "H₃" => specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y
local notation "L" => specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y
local notation "B₁" => specifiedCoconeLeftBranchLegHomotopy hp p c hc dB hB dC y
local notation "C₁" => specifiedCoconeLeftHomCylinderComparison hp p c hc dB dC y
local notation "D₁" => specifiedCoconeLeftAttachmentHomotopy hp p c hc dB dC y

/-- 左の元の HL・HR と枝比較の積は、同じ根辺・付加辺面円柱の積と同じ Arrow である。 -/
lemma specifiedCoconeLeftAttachment_original_homMk_comp_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy L) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy B₁)) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy C₁) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy D₁)) := by
  have hu := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq (functorHomotopyPostcomp H₀ P)
    (specifiedCoconeLeftUniversalHomotopy hp p c hc dB hB dC y)
    (specifiedCoconeLeftUniversalHomotopy_projection hp p c hc dB hB dC y).symm
  have hL := hu.trans (specifiedCoconeLeftUniversalHomotopy_hom_arrow hp p c hc dB hB dC y)
  have hBranch := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq (functorHomotopyPostcomp H₁ P) B₁
    ((specifiedCoconeLeftBranchToInitialHomotopy_projection hp p c hc dB hB dC y).trans
      (specifiedCoconeLeftBranchLegHomotopy_raw hp p c hc dB hB dC y).symm)
  have hD := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq (functorHomotopyPostcomp H₃ P) D₁
    (specifiedCoconeLeftAttachmentHomotopy_raw hp p c hc dB dC y).symm
  have ht := congrArg Arrow.mk
    (specifiedCoconeLeftAttachment_projection_homMk_comp hp p c hc dB hB dC y)
  exact (arrowComposition_congr hL hBranch).symm.trans
    (ht.trans (arrowComposition_congr rfl hD))
end

section
local notation "H₀" => specifiedCoconeRightUniversalInitialHomotopy hp p c hc dB dC hC y
local notation "H₁" => specifiedCoconeRightBranchToInitialHomotopy hp p c hc dB dC hC y
local notation "H₃" => specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y
local notation "L" => specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y
local notation "B₁" => specifiedCoconeRightBranchLegHomotopy hp p c hc dB dC hC y
local notation "C₁" => specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y
local notation "D₁" => specifiedCoconeRightAttachmentHomotopy hp p c hc dB dC y

/-- 右の元の HL・HR と枝比較の積は、同じ根辺・付加辺面円柱の積と同じ Arrow である。 -/
lemma specifiedCoconeRightAttachment_original_homMk_comp_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy L) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy B₁)) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy C₁) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy D₁)) := by
  have hu := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq (functorHomotopyPostcomp H₀ P)
    (specifiedCoconeRightUniversalHomotopy hp p c hc dB dC hC y)
    (specifiedCoconeRightUniversalHomotopy_projection hp p c hc dB dC hC y).symm
  have hL := hu.trans (specifiedCoconeRightUniversalHomotopy_hom_arrow hp p c hc dB dC hC y)
  have hBranch := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq (functorHomotopyPostcomp H₁ P) B₁
    ((specifiedCoconeRightBranchToInitialHomotopy_projection hp p c hc dB dC hC y).trans
      (specifiedCoconeRightBranchLegHomotopy_raw hp p c hc dB dC hC y).symm)
  have hD := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq (functorHomotopyPostcomp H₃ P) D₁
    (specifiedCoconeRightAttachmentHomotopy_raw hp p c hc dB dC y).symm
  have ht := congrArg Arrow.mk
    (specifiedCoconeRightAttachment_projection_homMk_comp hp p c hc dB dC hC y)
  exact (arrowComposition_congr hL hBranch).symm.trans
    (ht.trans (arrowComposition_congr rfl hD))
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
