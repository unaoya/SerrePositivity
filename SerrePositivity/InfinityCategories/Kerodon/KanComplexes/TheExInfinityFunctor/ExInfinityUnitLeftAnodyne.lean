module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.AnodyneKanTarget

/-!
概要：元のEx∞単位のleft anodyne性。
方針：検証済みのanodyne性とKan標的の一般補題を、元の同じ単位へ適用する。
規約：既存のEx∞関手と元の単位を変更しない。
使われ方：IS-W2 R03fの係数単位のbar上の相対比較。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 同じEx∞単位はleft anodyneであり、任意のleft fibrationへ相対延長できる。 -/
theorem exInfinityUnit_leftAnodyne (X : SSet.{u}) :
    leftAnodyneExtensions (exInfinityUnit.app X) :=
  anodyneExtensions_leftAnodyne_of_kanTarget _ (exInfinityUnit_anodyne X)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
