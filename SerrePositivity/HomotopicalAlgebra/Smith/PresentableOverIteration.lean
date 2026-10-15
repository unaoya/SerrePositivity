module

public import SerrePositivity.HomotopicalAlgebra.Smith.WeakReflectionApproximation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Bounded transfinite iteration over a fixed target

Colimits indexed by fewer than κ arrows retain κ-presentable domains. Thus
a short successor construction can run entirely within the presentable
objects over a fixed target, without a global accessible endofunctor.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.PresentableOverIteration
variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

abbrev property (X : C) : ObjectProperty (Over X) :=
  (isCardinalPresentable C κ).inverseImage (Over.forget X)

abbrev category (X : C) := (property κ X).FullSubcategory

lemma hasColimitsOfShape (X : C) (K : Type w) [SmallCategory K]
    (hK : HasCardinalLT (Arrow K) κ) : HasColimitsOfShape K (category κ X) := by
  have := isClosedUnderColimitsOfShape_isCardinalPresentable C hK
  have : (property κ X).IsClosedUnderColimitsOfShape K := inferInstance
  infer_instance

lemma inclusion_preservesColimitsOfShape (X : C) (K : Type w) [SmallCategory K]
    (hK : HasCardinalLT (Arrow K) κ) :
    PreservesColimitsOfShape K (property κ X).ι := by
  have := isClosedUnderColimitsOfShape_isCardinalPresentable C hK
  have : (property κ X).IsClosedUnderColimitsOfShape K := inferInstance
  infer_instance

lemma hasIterationOfShape (X : C) (J : Type w) [LinearOrder J]
    (hJ : HasCardinalLT J κ) : HasIterationOfShape J (category κ X) where
  hasColimitsOfShape := hasColimitsOfShape κ X J
    ((hasCardinalLT_arrow_iff_of_isThin J κ (Cardinal.IsRegular.aleph0_le Fact.out)).2 hJ)
  hasColimitsOfShape_of_isSuccLimit j _ := by
    have hj : HasCardinalLT (Set.Iio j) κ := hJ.of_injective Subtype.val Subtype.val_injective
    exact hasColimitsOfShape κ X (Set.Iio j)
      ((hasCardinalLT_arrow_iff_of_isThin _ κ (Cardinal.IsRegular.aleph0_le Fact.out)).2 hj)

end SerrePositivity.Smith.PresentableOverIteration
