module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.FixedTerminalHomotopyFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootVerticalHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeLeftRootEdgeFamily

/-!
概要：元の左三角形の全 Hom 族を、同じ根辺円柱全体へ延長する。
方針：長辺へ制限してから、底と終端係数を固定した相対 coslice の充填を使う。
規約：元の左族・根辺円柱・可変終点を保持する。使われ方：左右の全 Hom 作用の比較。
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
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫ L
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalHomotopy hp p c hc dB dC
local notation "z" => Subtype.val (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)
local notation "hz" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalHomotopy_terminal hp p c hc dB dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 同じ元の左三角形の全 Hom 族を、その実際の長辺へ制限する。 -/
def specifiedCoconeLeftRootTotalFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder W :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict L (stdSimplex.δ (1 : Fin 3))

/-- 制限後の底は、既存の左根辺族の同じ正規化表示である。 -/
lemma specifiedCoconeLeftRootTotalFamily_base :
    specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q ≫
        eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC)) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC)
  simp only [specifiedCoconeLeftRootTotalFamily, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFamily,
    ← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, Category.assoc]

/-- 同じ根辺円柱の底は、元の左長辺の時間に依存しない引き戻し。 -/
lemma specifiedCoconeRootVerticalFamily_base_diagram :
    fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ (W ≫ q) = (H).h ≫ q := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalHomotopy_projection]

local notation "hq" => specifiedCoconeRootVerticalFamily_base_diagram hp p c hc dB dC
local notation "a" => specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y

/-- 底・終端の全係数を保つ、同じ実際の根辺円柱上の全 Hom 族。 -/
def specifiedCoconeRootVerticalFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (H).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily H z hz q hq a

/-- 終端の族は元の左族の同じ引き戻しであり、時間に依存しない。 -/
lemma specifiedCoconeRootVerticalFamily_terminal :
    specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (H).h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1]) =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1])
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily_terminal_diagram H z hz) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily_terminal H z hz q hq a

/-- 底の全族も元の左長辺上の族の引き戻しそのもの。 -/
lemma specifiedCoconeRootVerticalFamily_base :
    specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (H).h q =
      (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (W ≫ q) (fst Δ[1] Δ[1]) hq :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily_base H z hz q hq a

/-- E 内の可変終点も、元の左三角形から得た同じ全族である。 -/
lemma specifiedCoconeRootVerticalFamily_projection :
    specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (H).h =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection L := by
  rw [specifiedCoconeRootVerticalFamily, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily_projection,
    specifiedCoconeLeftRootTotalFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection]

/-- 底の終点は全 Hom パラメータで元の指定 y のまま固定する。 -/
lemma specifiedCoconeRootVerticalFamily_fixed :
    (specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (H).h) ≫ q =
      SSet.const y := by
  rw [specifiedCoconeRootVerticalFamily_projection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily_fixed]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
