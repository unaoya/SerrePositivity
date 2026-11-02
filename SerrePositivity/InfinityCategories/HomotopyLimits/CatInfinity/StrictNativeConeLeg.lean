module

public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderDiagrams
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeLegs
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：通常の錐の coherent 表示の native な脚は元の脚の辺に一致する。
方針：標準脚の包含を Yoneda で射へ戻し、既存の脚の式を適用する。
規約：元の射の一単体と厳密に一致する。
使われ方：Cat_∞ の置換後の錐の二射影の読み戻し。 -/
lemma nativeConeLeg_strict {I : Type u} [SmallCategory I] {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C} (c : Cone F) (i : I) :
    (nativeConeLeg (HomotopyLimits.strictCoherentCone c)
      (ULift.up (ComposableArrows.mk₀ i))).edge = (coherentNerveEdge (c.π.app i)).edge := by
  change (HomotopyLimits.strictCoherentConeMap c).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (coneLegInclusion (ULift.up (ComposableArrows.mk₀ i)))) = _
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (HomotopyLimits.strictCoherentConeLeg c i) = _
  rw [HomotopyLimits.strictCoherentConeLeg_eq, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.F2
