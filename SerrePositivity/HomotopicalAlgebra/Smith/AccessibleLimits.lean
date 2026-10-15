module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleAdjunction
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFamilies
public import Mathlib.CategoryTheory.Presentable.Presheaf

/-! # Accessible limit functors in a locally presentable category

The shape is essentially small in the chosen accessibility universe.
Transport through a small model handles independent shape universes.
Filtered-colimit preservation of the limit functor follows from its actual
right adjunction, not from a blanket commutation assumption on the category.
-/

@[expose] public section
universe w s t v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.AccessibleLimits
variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C] [HasPullbacks C]
  (K : Type t) [Category.{s} K] [EssentiallySmall.{w} K]

lemma functorCategory_isLocallyPresentable : IsLocallyPresentable.{w} (K ⥤ C) := by
  let e := (equivSmallModel.{w} Kᵒᵖ).rightOp
  have : IsLocallyPresentable.{w} ((SmallModel.{w} Kᵒᵖ)ᵒᵖ ⥤ C) := inferInstance
  exact e.congrLeft.symm.isLocallyPresentable

lemma limitFunctor_isAccessible [HasLimitsOfShape K C] :
    (lim : (K ⥤ C) ⥤ C).IsAccessible.{w} := by
  have := functorCategory_isLocallyPresentable (C := C) K
  exact AccessibleAdjunction.rightAdjoint_isAccessible (constLimAdj (J := K) (C := C))

lemma pointwiseLimit_isAccessible [HasLimitsOfShape K C] [Small.{w} K]
    {D : Type u'} [Category.{v'} D] (F : K ⥤ D ⥤ C)
    [∀ k, (F.obj k).IsAccessible.{w}] : (F.flip ⋙ lim).IsAccessible.{w} := by
  have : ∀ k, (F.flip ⋙ (evaluation K C).obj k).IsAccessible.{w} :=
    fun k ↦ inferInstanceAs ((F.obj k).IsAccessible.{w})
  have := functorCategory_isAccessible F.flip
  have := limitFunctor_isAccessible (C := C) K
  infer_instance

end SerrePositivity.Smith.AccessibleLimits
