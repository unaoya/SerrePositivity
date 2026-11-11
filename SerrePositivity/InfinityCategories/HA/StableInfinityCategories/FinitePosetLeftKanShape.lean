module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FinitePosetLeftComma
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso

/-!
概要：有限順序添字の局所余極限から、元の図式に厳密に等しい左 Kan 拡張を得る。
方針：非退化単体の単射性と左 comma の包含で局所添字の有限性を証明する。
規約：元の図式と native な左 Kan 添字を保持する。使われ方：安定性の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ有限順序添字の全単体と局所余極限を保持する。 -/
lemma finitePosetLeftKanShape_finite {P Q : Type u} [PartialOrder P]
    [PartialOrder Q] [Finite P] (L : P ⥤ Q) (q : Q) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex q)).Finite :=
  SSet.finite_of_iso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso L q)

/-- 同じ有限順序添字の全単体と局所余極限を保持する。 -/
lemma finitePosetLeftKanShape_finite_at {P Q : Type u} [PartialOrder P]
    [PartialOrder Q] [Finite P] (L : P ⥤ Q) (c : (nerve Q) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap L) c).Finite := by
  obtain ⟨q, rfl⟩ := nerveEquiv.symm.surjective c
  exact finitePosetLeftKanShape_finite L q

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
