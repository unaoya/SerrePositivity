module
public import SerrePositivity.DifferentialGraded.Perfect.CompactRetracts
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift

/-! # compact dg導来対象の整数shift閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_equivalence (E : DerivedModuleCategory A D ≌ DerivedModuleCategory A D)
    [E.functor.Additive] {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    moduleCompact A D (E.functor.obj X) := by
  classical
  intro J F f
  let e := PreservesCoproduct.iso E.inverse F
  let b := E.toAdjunction.homEquiv X (∐ F) f
  obtain ⟨t, g, hg⟩ := hX J (fun j => E.inverse.obj (F j)) (b ≫ e.hom)
  refine ⟨t, fun j => (E.toAdjunction.homEquiv X (F j)).symm (g j), ?_⟩
  apply (E.toAdjunction.homAddEquiv X (∐ F)).injective
  calc
    _ = ∑ j ∈ t, g j ≫ E.inverse.map (Sigma.ι F j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (E.toAdjunction.homEquiv_naturality_right _ _).trans
        (by rw [Equiv.apply_symm_apply])
    _ = (∑ j ∈ t, g j ≫ Sigma.ι (fun j => E.inverse.obj (F j)) j) ≫ e.inv := by
      rw [sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Category.assoc, e, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
    _ = _ := by
      rw [hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl

lemma moduleCompact_shift {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) (n : ℤ) :
    moduleCompact A D (X⟦n⟧) := by
  let E := shiftEquiv (DerivedModuleCategory A D) n
  have : E.functor.Additive := by
    change (shiftFunctor (DerivedModuleCategory A D) n).Additive
    infer_instance
  exact moduleCompact_equivalence A D E hX

instance moduleCompactStableUnderShift : (moduleCompact A D).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ hX => moduleCompact_shift A D hX n⟩

end SerrePositivity.DifferentialGraded
