module

public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Monad.Limits

/-! # Completeness needed by Smith recognition

A small dense subcategory realizes a cocomplete category as a reflective
subcategory of presheaves. Shrinking hom universes makes the required colimits
exactly those provided by local presentability.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf
namespace SerrePositivity.Smith

lemma hasLimits_of_small_dense {C : Type u} [Category.{w} C]
    [HasColimitsOfSize.{w, w} C] {D : Type w} [SmallCategory D]
    (F : D ⥤ C) [F.IsDense] : HasLimitsOfSize.{w, w} C := by
  let Y := uliftYoneda.{w} (C := D)
  let L := Y.leftKanExtension F
  let : Reflective (restrictedULiftYoneda.{w} F) :=
    { L := L
      adj := uliftYonedaAdjunction L (Y.leftKanExtensionUnit F) }
  exact hasLimits_of_reflective (restrictedULiftYoneda.{w} F)

lemma locallyPresentable_hasLimits_sameHomUniverse {C : Type u} [Category.{w} C]
    [IsLocallyPresentable.{w} C] : HasLimitsOfSize.{w, w} C := by
  have := locallyPresentable_hasColimits (C := C)
  obtain ⟨κ, hκ, hC⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  let P := isCardinalPresentable C κ
  let F : SmallModel.{w} P.FullSubcategory ⥤ C :=
    (equivSmallModel P.FullSubcategory).inverse ⋙ P.ι
  have : F.IsDense := inferInstance
  exact hasLimits_of_small_dense F

lemma locallyPresentable_hasLimits {C : Type u} [Category.{v} C]
    [IsLocallyPresentable.{w} C] : HasLimitsOfSize.{w, w} C := by
  have : IsLocallyPresentable.{w} (ShrinkHoms C) :=
    (ShrinkHoms.equivalence.{w} C).isLocallyPresentable
  have := locallyPresentable_hasLimits_sameHomUniverse (C := ShrinkHoms C)
  exact Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence.{w} C).functor

end SerrePositivity.Smith
