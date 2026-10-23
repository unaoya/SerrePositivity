module
public import SerrePositivity.InfinityCategories.Stable.ExcisionSuspensionCospanShape
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawSuspensionSquare

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
namespace SerrePositivity.InfinityCategories

lemma excisionRawSuspensionSquare_eq_curry {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    excisionRawSuspensionSquare F = curry
      ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (Δ[1] ⊗ Δ[1])).hom ≫
        excisionGridSuspensionShape ≫ F) := by
  change curry (_ ≫ uncurry (curry (excisionGridSuspensionShape ≫ F))) = _
  rw [uncurry_curry]

lemma excisionRawSuspensionSquare_replaced_cospan {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F)) :
    pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c)) =
      pullbackCospan (excisionRawSuspensionSquare F) := by
  apply uncurry_injective
  simp only [pullbackCospan, excisionRawSuspensionSquare_eq_curry,
    uncurry_natural_left, uncurry_curry]
  simp only [← Category.assoc, BraidedCategory.braiding_naturality_right]
  have h := excisionReplaceInitial_comp_of_noninitial c
    (cospanSquareBoundary ▷ ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ≫ excisionGridSuspensionShape)
    excisionGridSuspensionFirstCospan_noninitial
  simpa only [Category.assoc] using congrArg
    (fun q ↦ (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (horn 2 2)).hom ≫ q) h

end SerrePositivity.InfinityCategories
