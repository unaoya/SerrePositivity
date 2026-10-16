module
public import SerrePositivity.DifferentialGraded.Perfect.CompactComparison
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-! # compact dg導来対象のretract・同型閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_of_retract {X Y : DerivedModuleCategory A D}
    (r : Retract X Y) (hY : moduleCompact A D Y) : moduleCompact A D X := by
  intro J F f
  obtain ⟨t, g, hg⟩ := hY J F (r.r ≫ f)
  refine ⟨t, fun j => r.i ≫ g j, ?_⟩
  calc
    _ = r.i ≫ ∑ j ∈ t, g j ≫ Sigma.ι F j := by
      rw [comp_sum]
      exact Finset.sum_congr rfl (fun j _ => Category.assoc _ _ _)
    _ = f := by rw [hg, ← Category.assoc, r.retract, Category.id_comp]

instance moduleCompactStableUnderRetracts : (moduleCompact A D).IsStableUnderRetracts where
  of_retract := moduleCompact_of_retract A D

instance moduleCompactClosedUnderIso : (moduleCompact A D).IsClosedUnderIsomorphisms :=
  inferInstance

lemma moduleCompact_of_isZero {X : DerivedModuleCategory A D} (hX : IsZero X) :
    moduleCompact A D X := by
  intro J F f
  refine ⟨∅, fun _ => 0, ?_⟩
  rw [Finset.sum_empty]
  exact hX.eq_of_src _ _

end SerrePositivity.DifferentialGraded
