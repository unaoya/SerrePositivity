module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueFamilySpecifiedFactors

/-!
概要：元の値比較の二つの端点表示を外し、同じ指定単位・余単位の値へ戻す。
方針：元の同じ表示変更の二つの型移送だけを除く。
規約：指定値を選び直さない。使われ方：元の余単位正方形と始点単位因子の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の始点因子は、同じ指定単位の元の全係数成分を値まで保つ。 -/
lemma pointedValueFamilySourceUnitIso_heq_unit (K : KanObject.{u}) {P : SSet.{u + 1}}
    (x : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
    HEq (pointedValueFamilySourceUnitIso K x)
      ((pointedValueRightComparison_unitIso (spaceInfinityVertex K)).precomp x) := by
  have hmp {α β : Sort (u + 2)} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
    cases h
    rfl
  have hmpr {α β : Sort (u + 2)} (h : α = β) (a : β) : HEq (Eq.mpr h a) a := by
    cases h
    rfl
  unfold pointedValueFamilySourceUnitIso
  exact (hmpr _ _).trans (hmp _ _)

/-- 元の終点因子は、同じ指定余単位の元の全値係数成分を値まで保つ。 -/
lemma pointedValueFamilyTargetCounitIso_heq_counit (L : KanObject.{u}) {P : SSet.{u + 1}}
    (v : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj L.obj) :
    HEq (pointedValueFamilyTargetCounitIso L v)
      ((pointedValueRightComparison_counitIso (spaceInfinityVertex L)).precomp v) := by
  have hmp {α β : Sort (u + 2)} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
    cases h
    rfl
  have hmpr {α β : Sort (u + 2)} (h : α = β) (a : β) : HEq (Eq.mpr h a) a := by
    cases h
    rfl
  unfold pointedValueFamilyTargetCounitIso
  exact (hmpr _ _).trans (hmp _ _)

end SerrePositivity.InfinityCategories.F2
