module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InverseSequenceQuasicategory
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InverseSequencePathDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ReplacementSpanComparison

/-!
概要：図式の可逆 path 置換の相対 corner を、既存の比較四角形の両端と同定する。
方針：二つの pullback の射影を比較して厳密な等式を得る。
規約：元の自然変換と隣接段の自然性を保持する。
使われ方：可算 inverse diagram の両端の極限比較の全境界持ち上げ。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet Opposite
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 自然な path 置換の始域への射影の相対 corner は、交換した始点比較そのもの。 -/
lemma inverseSequenceCorner_diagramPathProjection {F G : ℕᵒᵖ ⥤ SSet.{u}}
    (η : F ⟶ G) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequenceCorner (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequencePathProjection η) n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.replacementSquareStartCornerFlipped (η.app (op (n + 1))) (η.app (op n))
        (F.map (homOfLE (Nat.le_succ n)).op) (G.map (homOfLE (Nat.le_succ n)).op)
        (η.naturality (homOfLE (Nat.le_succ n)).op).symm := by
  apply pullback.hom_ext
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequenceCorner_fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequencePathProjection η) n).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.replacementSquareStartCornerFlipped_fst (η.app (op (n + 1))) (η.app (op n))
        (F.map (homOfLE (Nat.le_succ n)).op) (G.map (homOfLE (Nat.le_succ n)).op)
        (η.naturality (homOfLE (Nat.le_succ n)).op).symm).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequenceCorner_snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequencePathProjection η) n).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.replacementSquareStartCornerFlipped_snd (η.app (op (n + 1))) (η.app (op n))
        (F.map (homOfLE (Nat.le_succ n)).op) (G.map (homOfLE (Nat.le_succ n)).op)
        (η.naturality (homOfLE (Nat.le_succ n)).op).symm).symm

/-- 自然な path 置換の終点射影の相対 corner は、終点比較そのもの。 -/
lemma inverseSequenceCorner_diagramPathEndpoint {F G : ℕᵒᵖ ⥤ SSet.{u}}
    (η : F ⟶ G) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequenceCorner (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequencePathEndpoint η) n =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner (η.app (op (n + 1))) (η.app (op n))
        (F.map (homOfLE (Nat.le_succ n)).op) (G.map (homOfLE (Nat.le_succ n)).op)
        (η.naturality (homOfLE (Nat.le_succ n)).op).symm := by
  rfl

/-- 標的の遷移が相対 path を持ち上げれば、始点射影の相対 corner は全境界を持ち上げる。 -/
lemma trivialKanFibration_inverseSequenceCorner_projection {F G : ℕᵒᵖ ⥤ SSet.{u}}
    (η : F ⟶ G) (n : ℕ)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt
      (G.map (homOfLE (Nat.le_succ n)).op) 0)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequenceCorner (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequencePathProjection η) n) := by
  rw [inverseSequenceCorner_diagramPathProjection]
  infer_instance

/-- 同値な隣接比較と遷移の持ち上げから、終点射影の相対 corner は全境界を持ち上げる。 -/
lemma trivialKanFibration_inverseSequenceCorner_endpoint {F G : ℕᵒᵖ ⥤ SSet.{u}}
    [∀ j, Quasicategory (F.obj j)] [∀ j, Quasicategory (G.obj j)] (η : F ⟶ G) (n : ℕ)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app (op n))) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app (op (n + 1))))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (F.map (homOfLE (Nat.le_succ n)).op))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (G.map (homOfLE (Nat.le_succ n)).op)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequenceCorner (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.inverseSequencePathEndpoint η) n) := by
  rw [inverseSequenceCorner_diagramPathEndpoint]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_replacementSquareEndCorner _ _ _ _ _ h₁ h₀ hp hq

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
