module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeUniversalCommonRoot
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EvaluationFixedHomotopyTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootFamilyTriangle

/-!
概要：元の左右の根辺族から同じ native 普遍根辺族への二円柱と、元の比較の合成則。
方針：元の全族間円柱の二面を保持し、自明 Kan な終端制限の忠実性を使う。
規約：同じ元の根辺比較の類を回収。使われ方：指定経路の比較を共通根辺で貼り合わせる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y
local notation "root" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "rt" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y
local notation "Q" => Iso.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) d y)
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeUniversalCommonRootFamily hp p c hc dB dC y
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootFamilyComparison hp p c hc dB dC y

/-- 左の同じ全図式比較の根辺面を、厳密に共通する普遍根辺族への比較として保持する。 -/
def specifiedCoconeLeftUniversalCommonRootComparison : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y) W :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y)
    rfl (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftUniversalNativeFamily_root hp p c hc dB dC y)

/-- 右の同じ全図式比較の辺03も、同じ共通普遍根辺族への比較として保持する。 -/
def specifiedCoconeRightUniversalCommonRootComparison : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y) W :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y)
    rfl (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightUniversalNativeFamily_root hp p c hc dB dC y)

/-- 左の表示変更は、元の全図式比較の根辺面の raw な射を変えない。 -/
lemma specifiedCoconeLeftUniversalCommonRootComparison_raw :
    (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 右の表示変更も、元の全図式比較の辺03の raw な射を変えない。 -/
lemma specifiedCoconeRightUniversalCommonRootComparison_raw :
    (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 左の共通根辺比較は、元の同じ全 Hom の点図式係数を全時刻固定する。 -/
lemma specifiedCoconeLeftUniversalCommonRootComparison_terminal :
    (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y).h ≫ R =
      fst T Δ[1] ≫ Q := by
  rw [specifiedCoconeLeftUniversalCommonRootComparison_raw]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalRootFace_terminal hp p c hc dB dC y

/-- 右の共通根辺比較も、同じ全 Hom の点図式係数を全時刻固定する。 -/
lemma specifiedCoconeRightUniversalCommonRootComparison_terminal :
    (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y).h ≫ R =
      fst T Δ[1] ≫ Q := by
  rw [specifiedCoconeRightUniversalCommonRootComparison_raw]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalRootFace_terminal hp p c hc dB dC y

/-- 既存の根辺族比較も、表示を共通点図式へ揃えると同じ全時刻固定係数を持つ。 -/
lemma specifiedCoconeRootFamilyComparison_normalized_terminal :
    (G).h ≫ R = fst T Δ[1] ≫ Q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootFamilyComparison_target]
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq] using
    congrArg (fst T Δ[1] ≫ ·)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily_target hp p c hc dB dC y)

/-- 元の左右比較と右の共通根辺比較の合成は、左の同じ比較の類そのものである。 -/
lemma specifiedCoconeUniversalCommonRoot_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy G) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_of_rightAnodyne root (stdSimplex.δ (0 : Fin 2))
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram d) rt y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.evaluationFixedHomotopyTriangle_homMk_comp R G
    (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y)
    (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y) Q
    (specifiedCoconeRootFamilyComparison_normalized_terminal hp p c hc dB dC y)
    (specifiedCoconeRightUniversalCommonRootComparison_terminal hp p c hc dB dC y)
    (specifiedCoconeLeftUniversalCommonRootComparison_terminal hp p c hc dB dC y)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
