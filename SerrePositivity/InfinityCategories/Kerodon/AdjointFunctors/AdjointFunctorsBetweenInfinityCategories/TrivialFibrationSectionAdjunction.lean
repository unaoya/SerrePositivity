module

public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：自明 Kan fibration の厳密切断は左右両方の実随伴になる。
方針：全単射への持ち上げから相対始点・終点境界充填を得る。
規約：元の射影と指定切断を保持。使われ方：cofiber 図式の回転の随伴。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma initialBoundary_of_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (x : E _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x := by
  intro n a b _ sq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (boundary (n + 1)).ι inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

lemma terminalBoundary_of_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (x : E _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x := by
  intro n a b _ sq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (boundary (n + 1)).ι inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

variable {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)

/-- 指定切断が元の射影の左随伴になる。 -/
def trivialFibrationSectionLeftAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction s p :=
  adjunctionOfRelativeInitialSection hs (fun x =>
    initialBoundary_of_trivialKanFibration p (s.app (Opposite.op ⦋0⦌) x))

/-- 同じ指定切断が元の射影の右随伴にもなる。 -/
def trivialFibrationSectionRightAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction p s :=
  adjunctionOfRelativeTerminalSection hs (fun x =>
    terminalBoundary_of_trivialKanFibration p (s.app (Opposite.op ⦋0⦌) x))

end SerrePositivity.KST.LocalizingInvariants
