module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeLegs
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-!
概要：strict coherent 錐の native な脚と元の通常の射の一致。
方針：標準区間への制限と既存の strict な脚の式を使う。
規約：対象と Hom の宇宙を分ける。
使われ方：置換後の引き戻し錐の脚を通常の射影と同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity

/-- 概要：通常の錐の coherent 表示の native な脚は元の脚の辺に一致する。
方針：標準脚の包含を Yoneda で射へ戻し、既存の脚の式を適用する。
規約：元の射の一単体と厳密に一致する。
使われ方：Cat_∞ の置換後の錐の二射影の読み戻し。 -/
lemma nativeConeLeg_strict {I : Type u} [SmallCategory I] {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C} (c : Cone F) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)
      (ULift.up (ComposableArrows.mk₀ i))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (c.π.app i)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap c).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion (ULift.up (ComposableArrows.mk₀ i)))) = _
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg c i) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg_eq, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
