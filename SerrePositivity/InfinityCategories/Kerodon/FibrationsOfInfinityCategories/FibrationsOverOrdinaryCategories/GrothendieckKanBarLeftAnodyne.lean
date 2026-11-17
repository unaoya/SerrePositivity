module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanCoefficientLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementLeftAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityUnitLeftAnodyne

/-!
概要：元のCat図式のEx∞係数単位のbar上のleft anodyne性。
方針：元の同じ単位の各成分にR03f.2を適用する。
規約：係数関手・単位・simplicialReplacementMapを変更しない。
使われ方：IS-W2 R03fの元の相対延長の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor

/-- 元のEx∞係数単位による同じbarの全写像はleft anodyneである。 -/
theorem grothendieckKanCoefficientBarMap_leftAnodyne
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
    leftAnodyneExtensions (simplicialReplacementMap (grothendieckKanCoefficientUnit F)) := by
  apply simplicialReplacementMap_leftAnodyne
  intro i
  exact exInfinityUnit_leftAnodyne (nerve (F.obj i))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
