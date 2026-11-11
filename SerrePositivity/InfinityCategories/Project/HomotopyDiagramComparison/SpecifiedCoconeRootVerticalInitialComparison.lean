module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRetractionSectionComparison
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootVerticalInitialBase
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.TriangleLongEdge

/-!
概要：根辺円柱の始点側の全族を、時間零・一の同じ初期 Hom 係数の間で比較する。
方針：時間に依存しない底の厳密な等式を二切断の相対比較へ入力する。
規約：底と可変終点を全時刻固定する。使われ方：左右の元の Hom 作用への接続。
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
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "v" => Equiv.symm (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (f ≫ (i ≫ p)))) c
local notation "r" => stdSimplex.σ (0 : Fin 1)
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalInitialFamily hp p c hc dB dC y
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalInitialBaseFamily hp p c hc dB dC y
local notation "hb" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalInitialFamily_base hp p c hc dB dC y
local notation "s₀" => stdSimplex.δ (1 : Fin 2)
local notation "s₁" => stdSimplex.δ (0 : Fin 2)
local notation "h₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalRetraction_endpoint (1 : Fin 2)
local notation "h₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalRetraction_endpoint (0 : Fin 2)
local notation "P₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (r ≫ v) s₀
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamily_diagram v r s₀ h₀)
local notation "P₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (r ≫ v) s₁
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamily_diagram v r s₁ h₁)
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の根辺円柱の初期側で、二時刻の全余錐族を底を固定して結ぶ。 -/
def specifiedCoconeRootVerticalInitialComparison : SSet.Homotopy (a ≫ P₀) (a ≫ P₁) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionSectionComparison v r s₁ h₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne q a b hb s₀ h₀

/-- 比較の底は、元の時間零の初期 Hom の係数で全時刻固定する。 -/
lemma specifiedCoconeRootVerticalInitialComparison_base :
    (specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp v q = fst T Δ[1] ≫ (a ≫ P₀) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp v q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionSectionComparison_base v r s₁ h₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne
    q a b hb s₀ h₀

/-- 可変終点も元の初期時間辺の同じ全族のまま保持する。 -/
lemma specifiedCoconeRootVerticalInitialComparison_projection :
    (specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection v = fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionSectionComparison_projection v r s₁ h₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne
    q a b hb s₀ h₀

/-- 比較の底の終点も、元の y の上で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalInitialComparison_fixed :
    ((specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection v) ≫ q = SSet.const y := by
  rw [specifiedCoconeRootVerticalInitialComparison_projection]
  have h := congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalInitialFamily_fixed hp p c hc dB dC y)
  simpa only [Category.assoc, SSet.comp_const] using h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
