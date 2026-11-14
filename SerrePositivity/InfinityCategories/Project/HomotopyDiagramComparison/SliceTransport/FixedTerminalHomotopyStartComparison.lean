module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.FixedTerminalHomotopyStart
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.RelativeCosliceFamilyHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.TriangleLongEdge

/-!
概要：根辺円柱へ延長した族の時間零の端面を、元の全族と相対的に結ぶ。
方針：端面で証明した終端・底の等式を相対 coslice 比較へ入力する。
規約：終端・底・可変終点を全時刻で保持する。使われ方：元の左 Hom 族との接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B T : SSet.{u}} {W V : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy W V) (z : E _⦋0⦌)
  (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ H.h = SSet.const z)
  (q : E ⟶ B) [InnerFibration q]
  (hq : fst (Δ[1] : SSet.{u}) Δ[1] ≫ (W ≫ q) = H.h ≫ q)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder W)
local notation "a₀" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyStartFamily H z hz q hq a
local notation "k" => stdSimplex.δ (0 : Fin 2)

/-- 時間零の端面と元の族を、終端と底の上で定値なホモトピーで結ぶ。 -/
lemma exists_fixedTerminalHomotopyStartComparison :
    ∃ K : SSet.Homotopy a₀ a,
      K.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W k = fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W k ∧
      K.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q = fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_relativeCosliceFamilyHomotopy W q k _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne a₀ a
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyStartFamily_terminal H z hz q hq a)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyStartFamily_base H z hz q hq a)

/-- 同じ元の族を保つ、時間零の端面の実際の相対比較円柱。 -/
def fixedTerminalHomotopyStartComparison : SSet.Homotopy a₀ a :=
  (exists_fixedTerminalHomotopyStartComparison H z hz q hq a).choose

/-- 終端の全係数を全時刻固定する。 -/
lemma fixedTerminalHomotopyStartComparison_terminal :
    (fixedTerminalHomotopyStartComparison H z hz q hq a).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W k =
      fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W k :=
  (exists_fixedTerminalHomotopyStartComparison H z hz q hq a).choose_spec.1

/-- 底の全余錐族も全時刻固定する。 -/
lemma fixedTerminalHomotopyStartComparison_base :
    (fixedTerminalHomotopyStartComparison H z hz q hq a).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q =
      fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q :=
  (exists_fixedTerminalHomotopyStartComparison H z hz q hq a).choose_spec.2

/-- 可変終点の全族も同じ比較円柱の全時刻で保持する。 -/
lemma fixedTerminalHomotopyStartComparison_projection :
    (fixedTerminalHomotopyStartComparison H z hz q hq a).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W =
      fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection W k, ← Category.assoc,
    fixedTerminalHomotopyStartComparison_terminal, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
