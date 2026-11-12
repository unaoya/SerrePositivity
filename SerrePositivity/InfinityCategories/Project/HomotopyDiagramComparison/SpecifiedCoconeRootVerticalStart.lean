module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedTerminalHomotopyStartComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootVerticalFamily

/-!
概要：同じ根辺円柱の時間零の端面を、元の左三角形の全 Hom 族へ相対的に接続する。
方針：底と終端の厳密な一致を用いる比較を、元の同じ具体的な円柱と族へ適用する。
規約：終端・底・可変終点を全時刻固定する。使われ方：指定余極限の全 Hom 作用の照合。
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
local notation "hq" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily_base_diagram hp p c hc dB dC
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の同じ根辺円柱上の全 Hom 族の、時間零の実際の端面。 -/
def specifiedCoconeRootVerticalStartFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder W :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (H).h SSet.ι₀ (H).h₀

/-- 元の左三角形の長辺族へ、終端と底を固定して戻す実際の円柱。 -/
def specifiedCoconeRootVerticalStartComparison :
    SSet.Homotopy (specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y) a :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyStartComparison H z hz q hq a

/-- 比較は元の左長辺族の終端係数を全時刻で保持する。 -/
lemma specifiedCoconeRootVerticalStartComparison_terminal :
    (specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) =
      fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyStartComparison_terminal H z hz q hq a

/-- 比較は元の左長辺族の底も全時刻で保持する。 -/
lemma specifiedCoconeRootVerticalStartComparison_base :
    (specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q = fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyStartComparison_base H z hz q hq a

/-- 可変終点は、元の左三角形の同じ全 Hom 族のまま全時刻で固定する。 -/
lemma specifiedCoconeRootVerticalStartComparison_projection :
    (specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W =
      fst T Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection L := by
  simp only [specifiedCoconeRootVerticalStartComparison,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyStartComparison_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection]

/-- 比較の底の終点も、元の指定 y で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalStartComparison_fixed :
    ((specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W) ≫ q = SSet.const y := by
  rw [specifiedCoconeRootVerticalStartComparison_projection]
  have h := congrArg (fun k ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y)
  simpa only [Category.assoc, SSet.comp_const] using h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
