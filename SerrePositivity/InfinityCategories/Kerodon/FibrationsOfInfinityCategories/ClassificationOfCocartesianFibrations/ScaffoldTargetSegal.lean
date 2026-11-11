module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldLargeOverIsos
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeHomPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramAnodyneRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningHomInterval

/-!
概要：同じ分類図式の区間 Hom を、全次元で最初の辺と尾部の pullback へ制限する。
方針：同じ大きい比較への制限と厳密 pullback 表示を合成する。
規約：元の分類図式と両端固定の全パラメーターを保持する。
使われ方：高次単体の元の分類 Hom 作用の同値性を反映する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLargeBridge n k

/-- 同じ分類図式間の全区間 Hom から、最初の区間と尾部の厳密 pullback への射。 -/
def cocartesianScaffoldTargetSegalMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex P) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex Q) ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.toFirst n H))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.toTail n H)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction H P Q ≫
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.intervalDiagram_isPullback n H P Q).isoPullback.hom

/-- 同じ target Segal 射の最初の射影は、元の同じ区間への直接制限。 -/
lemma cocartesianScaffoldTargetSegalMap_fst :
    cocartesianScaffoldTargetSegalMap n k p q ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.first n H).hom P Q := by
  rw [cocartesianScaffoldTargetSegalMap, Category.assoc, IsPullback.isoPullback_hom_fst]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_restriction P Q (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.firstInclusion n H)

/-- 同じ target Segal 射の尾部射影も、元の同じ尾部への直接制限。 -/
lemma cocartesianScaffoldTargetSegalMap_snd :
    cocartesianScaffoldTargetSegalMap n k p q ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.tail n H).hom P Q := by
  rw [cocartesianScaffoldTargetSegalMap, Category.assoc, IsPullback.isoPullback_hom_snd]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_restriction P Q (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldBridgeOver.tailInclusion n H)

/-- 全次元で、恒等セル上の同じ target Segal 制限は自明 Kan。 -/
lemma cocartesianScaffoldTargetSegalMap_id_trivialKanFibration
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 2))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cocartesianScaffoldTargetSegalMap n (𝟭 _) p q) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_trivialKanFibration_of_innerAnodyne
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLargeBridge n (𝟭 (ULift.{u} (Fin (n + 2)))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLargeBridge_id_innerAnodyne n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ h.mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
