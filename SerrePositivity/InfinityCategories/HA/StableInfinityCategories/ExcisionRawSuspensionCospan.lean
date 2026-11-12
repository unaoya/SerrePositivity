module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSuspensionCospanShape
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRawSuspensionSquare

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionRawSuspensionSquare_eq_curry {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare F = curry
      ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (Δ[1] ⊗ Δ[1])).hom ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape ≫ F) := by
  change curry (_ ≫ uncurry (curry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape ≫ F))) = _
  rw [uncurry_curry]

lemma excisionRawSuspensionSquare_replaced_cospan {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare F) := by
  apply uncurry_injective
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, excisionRawSuspensionSquare_eq_curry,
    uncurry_natural_left, uncurry_curry]
  simp only [← Category.assoc, BraidedCategory.braiding_naturality_right]
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_comp_of_noninitial c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ▷ ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionFirstCospan_noninitial
  simpa only [Category.assoc] using congrArg
    (fun q ↦ (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (horn 2 2)).hom ≫ q) h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
