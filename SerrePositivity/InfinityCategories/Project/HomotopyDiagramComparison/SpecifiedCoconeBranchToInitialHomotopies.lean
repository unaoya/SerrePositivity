module

public import
  SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentTotalPrecomposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeLeftBranchHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRightBranchHom

/-!
概要：元の左右の枝の Hom 比較円柱に、実際の付加比較辺を同時に前置する。
方針：初期 Hom 間の前置写像へ同じ円柱を後合成し、評価と底の raw な式を計算する。
規約：枝の元の円柱と付加辺の既存の前合成を保持。使われ方：native 根辺比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB)
  (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "qA" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "qB" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p)
local notation "qC" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y
local notation "UL" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y
local notation "UR" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j y
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "RL" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (i ≫ p) f rfl y
local notation "RR" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y
local notation "DB" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchHomCylinderData hp p c hc dB hB dC y
local notation "DC" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchHomCylinderData hp p c hc dB dC hC y
local notation "ΦL" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition c hc f (i ≫ p) rfl dB y
local notation "ΦR" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition c hc g (j ≫ p)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC y
local notation "PA" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection qA c y ≫
  Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso qA c y)

/-- 元の左枝の同じ評価固定円柱を、付加比較辺で共通始対象の初期 Hom へ写す。 -/
def specifiedCoconeLeftBranchToInitialHomotopy : SSet.Homotopy
    ((UL ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection qB dB hB y) ≫ ΦL)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y ≫ ΦL) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (DB).homotopy ΦL

/-- 右も、元の同じ枝円柱と実際の右付加辺を使う。 -/
def specifiedCoconeRightBranchToInitialHomotopy : SSet.Homotopy
    ((UR ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection qC dC hC y) ≫ ΦR)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchInitialHomFamily hp p c hc dB dC y ≫ ΦR) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (DC).homotopy ΦR

/-- 左枝の前置後も、同じ共通終点の全族を円柱の全時刻で保持する。 -/
lemma specifiedCoconeLeftBranchToInitialHomotopy_evaluation :
    (specifiedCoconeLeftBranchToInitialHomotopy hp p c hc dB hB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qA c y = fst T Δ[1] ≫ V := by
  have hv : UL ≫ RL = V := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id,
      Category.assoc] using (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonHomFamily_eq hp p c hc dB dC y)
  change ((DB).homotopy.h ≫ ΦL) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qA c y = _
  calc
    _ = (DB).homotopy.h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qB dB y ≫ RL) :=
      (Category.assoc _ _ _).trans (congrArg ((DB).homotopy.h ≫ ·)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition_evaluation c hc f (i ≫ p) rfl dB y))
    _ = ((DB).homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qB dB y) ≫ RL :=
      (Category.assoc _ _ _).symm
    _ = (fst T Δ[1] ≫ UL) ≫ RL := congrArg (· ≫ RL) (DB).evaluation
    _ = _ := (Category.assoc _ _ _).trans (congrArg (fst T Δ[1] ≫ ·) hv)

/-- 右枝の前置後も、全く同じ共通終点の全族を全時刻で評価する。 -/
lemma specifiedCoconeRightBranchToInitialHomotopy_evaluation :
    (specifiedCoconeRightBranchToInitialHomotopy hp p c hc dB dC hC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qA c y = fst T Δ[1] ≫ V := by
  have hv : UR ≫ RR = V := Category.assoc _ _ _
  change ((DC).homotopy.h ≫ ΦR) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qA c y = _
  calc
    _ = (DC).homotopy.h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qC dC y ≫ RR) :=
      (Category.assoc _ _ _).trans (congrArg ((DC).homotopy.h ≫ ·)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition_evaluation c hc g (j ≫ p)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC y))
    _ = ((DC).homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation qC dC y) ≫ RR :=
      (Category.assoc _ _ _).symm
    _ = (fst T Δ[1] ≫ UR) ≫ RR := congrArg (· ≫ RR) (DC).evaluation
    _ = _ := (Category.assoc _ _ _).trans (congrArg (fst T Δ[1] ≫ ·) hv)

/-- 左枝の底は、元の同じ枝 Hom 円柱に既存の付加辺の前合成を続けた raw な射。 -/
lemma specifiedCoconeLeftBranchToInitialHomotopy_projection :
    (specifiedCoconeLeftBranchToInitialHomotopy hp p c hc dB hB dC y).h ≫ PA =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchHomotopy hp p c hc dB hB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftBranchHomotopy_projection]
  have h := congrArg ((DB).homotopy.h ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition_pinched c hc f (i ≫ p) rfl dB y)
  simpa only [specifiedCoconeLeftBranchToInitialHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp,
    Category.assoc] using h

/-- 右も、同じ元の枝 Hom 円柱の既存の付加辺による raw な像そのもの。 -/
lemma specifiedCoconeRightBranchToInitialHomotopy_projection :
    (specifiedCoconeRightBranchToInitialHomotopy hp p c hc dB dC hC y).h ≫ PA =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchHomotopy hp p c hc dB dC hC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentHomPrecomposition c hc g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchHomotopy_projection]
  have h := congrArg ((DC).homotopy.h ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTotalPrecomposition_pinched c hc g (j ≫ p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC y)
  simpa only [specifiedCoconeRightBranchToInitialHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp,
    Category.assoc] using h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
