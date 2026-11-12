module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLiftingClosure
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Filtered-colimit closure of the original weak equivalences

A specified trivial-cofibration/fibration factorization detects weak
 equivalences by its right factor. This proves closure and accessibility of
 the inclusion, but not yet accessibility of the weak-equivalence category.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Smith.WeakEquivalenceFilteredColimits
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (d : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

lemma weakEquivalence_iff_rightFactor (f : Arrow C) :
    weakEquivalences C f.hom ↔ trivialFibrations C (d.p.app f) := by
  have hi : weakEquivalences C (d.i.app f) := (d.hi f).2
  have h := (weakEquivalences C).precomp_iff (W' := weakEquivalences C)
    (d.i.app f) (d.p.app f) hi
  rw [d.fac_app] at h
  exact ⟨fun hf ↦ ⟨d.hp f, h.1 hf⟩, fun hf ↦ h.2 hf.2⟩

lemma arrowProperty_eq_inverseImage (I : MorphismProperty C)
    (hI : I.rlp = trivialFibrations C) :
    arrowProperty (weakEquivalences C) =
      (arrowProperty I.rlp).inverseImage (AccessibleFactorization.rightFactor d) := by
  funext f
  apply propext
  change weakEquivalences C f.hom ↔ I.rlp (d.p.app f)
  rw [hI]
  exact weakEquivalence_iff_rightFactor d f

variable [HasColimitsOfSize.{w, w} C]
  (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [d.Z.IsCardinalAccessible κ]
  [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
  [∀ i : I.toSet, IsCardinalPresentable i.val.right κ]

include d I hI

lemma closedUnderColimitsOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    (arrowProperty (weakEquivalences C)).IsClosedUnderColimitsOfShape J := by
  rw [arrowProperty_eq_inverseImage d I hI]
  have := AccessibleLiftingClosure.closedUnderColimitsOfShape I κ (J := J)
  have := AccessibleFactorization.rightFactor_isCardinalAccessible d κ
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (AccessibleFactorization.rightFactor d) κ J
  infer_instance

lemma hasCardinalFilteredColimits :
    HasCardinalFilteredColimits.{w} (arrowProperty (weakEquivalences C)).FullSubcategory κ where
  hasColimitsOfShape J _ _ := by
    have := closedUnderColimitsOfShape d I hI κ J
    infer_instance

lemma inclusion_isCardinalAccessible :
    (arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := closedUnderColimitsOfShape d I hI κ J
    infer_instance

end SerrePositivity.Smith.WeakEquivalenceFilteredColimits

namespace SerrePositivity.Smith

/-- The original weak-equivalence category has sufficiently filtered colimits,
and its actual full inclusion preserves them. This does not assert a small
presentable generating family for that category. -/
lemma exists_weakEquivalence_filtered_colimits
    {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      HasCardinalFilteredColimits.{w} (arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
      (arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := C)
  have : I.IsSmall.{w} := by
    obtain ⟨μ, hμ, hb, hI⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := I)
    exact SmallObject.isSmall I μ
  obtain ⟨κ₀, h₀, ⟨d⟩⟩ := exists_accessible_model_factorizations C I J
  obtain ⟨κ₁, h₁, ha⟩ := exists_common_arrow_presentability (fun i : I.toSet ↦ i.val)
  let κ := max κ₀ κ₁
  have : Fact κ.IsRegular := ⟨by
    rcases le_total κ₀ κ₁ with h | h
    · simpa only [κ, max_eq_right h] using h₁.out
    · simpa only [κ, max_eq_left h] using h₀.out⟩
  let d' := d.atLarger κ (le_max_left _ _)
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.left κ := fun i ↦ by
    have := (ha i).1
    exact isCardinalPresentable_of_le _ (le_max_right _ _)
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.right κ := fun i ↦ by
    have := (ha i).2
    exact isCardinalPresentable_of_le _ (le_max_right _ _)
  have := d'.fibrationAccessible
  have hI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)
  exact ⟨κ, inferInstance,
    WeakEquivalenceFilteredColimits.hasCardinalFilteredColimits d'.fibrationData I hI κ,
    WeakEquivalenceFilteredColimits.inclusion_isCardinalAccessible d'.fibrationData I hI κ⟩

end SerrePositivity.Smith
