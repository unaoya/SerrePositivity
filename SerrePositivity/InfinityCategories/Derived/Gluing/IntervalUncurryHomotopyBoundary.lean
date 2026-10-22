module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryHomotopy

/-! 実区間評価後の同じホモトピーは、区間の両端を全時刻で固定する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {K X : SSet.{u}} {x y : X _⦋0⦌}
  {f g : K ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g)

lemma dgGluingIntervalUncurryHomotopy_source :
    (prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
        (dgGluingIntervalUncurryHomotopy H).h = SSet.const x := by
  have hi : (prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom =
    prismEndpoint 0 (K ⊗ (Δ[1] : SSet.{u})) := rfl
  change _ ≫ ((α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom ≫
    intervalMappingUncurry H.h) = _
  rw [← Category.assoc, hi, intervalFamily_zero]

lemma dgGluingIntervalUncurryHomotopy_target :
    (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
        (dgGluingIntervalUncurryHomotopy H).h = SSet.const y := by
  have hi : (prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫
      (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom =
    prismEndpoint 1 (K ⊗ (Δ[1] : SSet.{u})) := rfl
  change _ ≫ ((α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom ≫
    intervalMappingUncurry H.h) = _
  rw [← Category.assoc, hi, intervalFamily_one]

end SerrePositivity.InfinityCategories
