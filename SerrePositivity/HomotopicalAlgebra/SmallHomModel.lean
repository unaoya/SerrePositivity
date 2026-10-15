module

public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-! # The existing model structure in a chosen small Hom universe

Mathlib's ShrinkHoms equivalence changes only the representation of Hom
sets. The three morphism classes are inverse images of the original ones,
and Mathlib transports every model axiom. Local presentability and its
colimits transport as well; no relation between the old Hom universe v
and the accessibility universe w is imposed.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SmallHomModel
variable (C : Type u) [Category.{v} C] [ModelCategory C] [LocallySmall.{w} C]

abbrev equivalence : ShrinkHoms C ≌ C := (ShrinkHoms.equivalence.{w} C).symm

@[instance_reducible]
def modelCategory : ModelCategory (ShrinkHoms C) := by
  let e := equivalence C
  let : CategoryWithCofibrations (ShrinkHoms C) := ⟨(cofibrations C).inverseImage e.functor⟩
  let : CategoryWithFibrations (ShrinkHoms C) := ⟨(fibrations C).inverseImage e.functor⟩
  let : CategoryWithWeakEquivalences (ShrinkHoms C) := ⟨(weakEquivalences C).inverseImage e.functor⟩
  exact ModelCategory.transport e rfl rfl rfl

lemma modelCategory_cofibrations : (modelCategory.{w} C).categoryWithCofibrations.cofibrations =
    (cofibrations C).inverseImage (equivalence.{w} C).functor := rfl

lemma modelCategory_fibrations : (modelCategory.{w} C).categoryWithFibrations.fibrations =
    (fibrations C).inverseImage (equivalence.{w} C).functor := rfl

lemma modelCategory_weakEquivalences :
    (modelCategory.{w} C).categoryWithWeakEquivalences.weakEquivalences =
      (weakEquivalences C).inverseImage (equivalence.{w} C).functor := rfl

lemma toOriginal_isLeftQuillen :
    let := modelCategory.{w} C
    Quillen.IsLeftQuillen (equivalence.{w} C).functor := by
  let := modelCategory.{w} C
  exact ⟨fun _ _ _ hf => hf, fun _ _ _ hf => hf⟩

lemma toOriginal_isRightQuillen :
    let := modelCategory.{w} C
    Quillen.IsRightQuillen (equivalence.{w} C).functor := by
  let := modelCategory.{w} C
  exact ⟨fun _ _ _ hf => hf, fun _ _ _ hf => hf⟩

lemma fromOriginal_isLeftQuillen :
    let := modelCategory.{w} C
    Quillen.IsLeftQuillen (equivalence.{w} C).inverse := by
  let := modelCategory.{w} C
  have : Quillen.IsRightQuillen (equivalence.{w} C).symm.inverse :=
    toOriginal_isRightQuillen.{w} C
  exact Quillen.isLeftQuillen_of_isRightQuillen (equivalence.{w} C).symm.toAdjunction

lemma fromOriginal_isRightQuillen :
    let := modelCategory.{w} C
    Quillen.IsRightQuillen (equivalence.{w} C).inverse := by
  let := modelCategory.{w} C
  have := toOriginal_isLeftQuillen.{w} C
  exact Quillen.isRightQuillen_of_isLeftQuillen (equivalence.{w} C).toAdjunction

omit [ModelCategory C] in
lemma locallyPresentable [IsLocallyPresentable.{w} C] :
    IsLocallyPresentable.{w} (ShrinkHoms C) :=
  (ShrinkHoms.equivalence.{w} C).isLocallyPresentable

omit [ModelCategory C] in
lemma realizationColimits [IsLocallyPresentable.{w} C] :
    HasColimitsOfSize.{0, w} (ShrinkHoms C) := by
  have := locallyPresentable.{w} C
  have := Smith.locallyPresentable_hasColimits (C := ShrinkHoms C)
  exact hasColimitsOfSizeShrink.{0, w} (ShrinkHoms C)

end SerrePositivity.SmallHomModel
