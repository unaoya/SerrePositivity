module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingOverNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSlicePostcompIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceOverEqualityTransport

/-!
概要：right fibration の写像空間の span を、同じ底上の射に沿って比較する。
方針：終点を正規化した slice 後合成を頂点 fiber に制限し、全族の持ち上げを比較する。
規約：選択した切断そのものの厳密な自然性は要求しない。
使われ方：Kerodon §7.4 の表現可能比較、G8 の固定端点錐の族の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：射影が等式で与えられた底上の射でも、同じ表現可能比較は全族で可換。
方針：射影の等式を消去し、共通の自明 Kan fibration 上の同じ切断比較を使う。
規約：終点の等式は Hom の厳密な移送で保持する。
使われ方：G8 の正規化した錐制限。 -/
def rightFibrationHomComparison_overMapIso_of_eq {E F B : SSet.{u}}
    (r : E ⟶ B) (s : F ⟶ B) (f : E ⟶ F) (hf : f ≫ s = r)
    [RightFibration r] [RightFibration s] (c : E _⦋0⦌) (x : B _⦋0⦌) :
    FunctorIso
      (rightFibrationHomComparison r c x ≫ vertexFiberMap r s f hf x)
      (eqToHom (congrArg (fun t : E ⟶ B => Basic.pinchedHom x (t.app _ c)) hf.symm) ≫
        rightFibrationHomComparison s (f.app _ c) x) := by
  subst r
  simpa only [eqToHom_refl, Category.id_comp] using
    rightFibrationHomComparison_overMapIso f s c x

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
