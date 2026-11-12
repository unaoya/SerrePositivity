module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeRetractCosliceFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.PrismEndpointRightAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono

/-!
概要：終点を固定した同じ根辺円柱へ、元の全余錐族を延長する。
方針：終端包含の right anodyne 性と相対 coslice の充填を使う。
規約：底と終点係数の全族を厳密に保つ。使われ方：指定余極限の全 Hom 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 空間の終端を時刻零へ移す二つの包含は、同じ正方形の頂点である。 -/
lemma terminalPrism_initialTime :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ fst Δ[1] Δ[1]) ≫ SSet.ι₀ =
      (SSet.const (stdSimplex.obj₀Equiv.symm 0) : Δ[1] ⟶ Δ[1]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

variable {E B T : SSet.{u}} {W V : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy W V) (z : E _⦋0⦌)
  (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ H.h = SSet.const z)

include hz in
/-- 終点固定の円柱は、元の辺と同じ終端図式を厳密に持つ。 -/
lemma fixedTerminalHomotopyFamily_terminal_diagram :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ fst Δ[1] Δ[1]) ≫ W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ H.h := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1]) ≫ (SSet.ι₀ ≫ H.h) :=
      congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1]) ≫ k) H.h₀.symm
    _ = _ := by
      rw [← Category.assoc, terminalPrism_initialTime, Category.assoc, hz,
        SSet.comp_const]

variable (q : E ⟶ B) [InnerFibration q]
  (hq : fst (Δ[1] : SSet.{u}) Δ[1] ≫ (W ≫ q) = H.h ≫ q)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder W)

/-- 底と終点係数を保つ、同じ円柱上の全パラメータの余錐族。 -/
def fixedTerminalHomotopyFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder H.h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeRetractCosliceFamily q H.h W (fst Δ[1] Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.prismEndpoint_one_rightAnodyne Δ[1]) hq
    (fixedTerminalHomotopyFamily_terminal_diagram H z hz) a

/-- 終端の全係数は、元の族の同じ終端への引き戻しである。 -/
lemma fixedTerminalHomotopyFamily_terminal :
    fixedTerminalHomotopyFamily H z hz q hq a ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict H.h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1]) =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1])
        (fixedTerminalHomotopyFamily_terminal_diagram H z hz) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeRetractCosliceFamily_terminal _ _ _ _ _ _ _ _ _

/-- 底は元の全余錐族の時間に依存しない引き戻しである。 -/
lemma fixedTerminalHomotopyFamily_base :
    fixedTerminalHomotopyFamily H z hz q hq a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp H.h q =
      (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (W ≫ q) (fst Δ[1] Δ[1]) hq :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeRetractCosliceFamily_base _ _ _ _ _ _ _ _ _

/-- 可変終点も元の E 内の全族のまま保つ。 -/
lemma fixedTerminalHomotopyFamily_projection :
    fixedTerminalHomotopyFamily H z hz q hq a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection H.h =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeRetractCosliceFamily_projection _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
