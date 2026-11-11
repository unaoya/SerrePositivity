module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedTerminalHomotopyEnd
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootVerticalFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootEdgeFamily

/-!
概要：同じ根辺円柱の時間一の端面と、元の右四面体の長辺族を明示する。
方針：各族を同じ実際の右長辺上に置き、底を既存の左右の根辺族へ照合する。
規約：両族の一致はまだ主張しない。使われ方：終端固定の底の比較の持ち上げ。
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
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge ≫ R
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalHomotopy hp p c hc dB dC
local notation "z" => Subtype.val (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)
local notation "hz" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalHomotopy_terminal hp p c hc dB dC
local notation "hq" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily_base_diagram hp p c hc dB dC
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y
local notation "hV" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC

/-- 元の同じ根辺円柱の全族の、時間一の実際の右長辺上の端面。 -/
def specifiedCoconeRootVerticalEndFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder V :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (H).h SSet.ι₁ (H).h₁

/-- 時間一の端面の底は、元の左根辺の全 Hom 族そのもの。 -/
lemma specifiedCoconeRootVerticalEndFamily_base :
    (specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp V q) ≫
        eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hV) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom hV]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyEndFamily H z hz q hq a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp V q) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyEndFamily_base,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopy_end_base_diagram H q hq)]
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily_base hp p c hc dB dC y)
  simp only [← Category.assoc] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC)] at h
  exact h

/-- 時間一でも元の全族の同じ終端係数を保持する。 -/
lemma specifiedCoconeRootVerticalEndFamily_terminal :
    specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict V (stdSimplex.δ (0 : Fin 2)) =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction
        (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC)
        (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopy_end_terminal_diagram H z hz) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyEndFamily_terminal H z hz q hq a

/-- 時間一の端面も元の左三角形の可変終点の全族を保持する。 -/
lemma specifiedCoconeRootVerticalEndFamily_projection :
    specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection V =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC) := by
  change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyEndFamily H z hz q hq a ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyEndFamily_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection]

/-- 比較先となる元の右四面体の、同じ実際の長辺上の全 Hom 族。 -/
def specifiedCoconeRightRootTotalFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder V :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict R _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge

/-- 元の右族の底は、既存の右根辺の全族の同じ正規化表示。 -/
lemma specifiedCoconeRightRootTotalFamily_base :
    (specifiedCoconeRightRootTotalFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp V q) ≫
        eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hV) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC)
  simp only [specifiedCoconeRightRootTotalFamily, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFamily]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom hV, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
