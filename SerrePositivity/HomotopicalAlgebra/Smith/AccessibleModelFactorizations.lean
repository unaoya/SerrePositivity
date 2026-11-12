module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleGeneratedPair

/-! # Accessible model factorizations and replacements

The specified data supply both model factorizations, their four arrow factors,
and cofibrant/fibrant replacement at one regular cardinal. An arbitrary choice
of functorial factorization is not asserted to be accessible.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Smith
variable (C : Type u) [Category.{v} C] [ModelCategory C]

structure AccessibleModelFactorizations (κ : Cardinal.{w}) [Fact κ.IsRegular] where
  cofibrationData : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C)
  fibrationData : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C)
  cofibrationAccessible : cofibrationData.Z.IsCardinalAccessible κ
  fibrationAccessible : fibrationData.Z.IsCardinalAccessible κ

namespace AccessibleModelFactorizations
variable {C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
  (d : AccessibleModelFactorizations C κ)

/-- The same specified data work at every larger regular cardinal. -/
def atLarger (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ') :
    AccessibleModelFactorizations C κ' where
  cofibrationData := d.cofibrationData
  fibrationData := d.fibrationData
  cofibrationAccessible := by
    have := d.cofibrationAccessible
    exact d.cofibrationData.Z.isCardinalAccessible_of_le h
  fibrationAccessible := by
    have := d.fibrationAccessible
    exact d.fibrationData.Z.isCardinalAccessible_of_le h

abbrev Q : C ⥤ C := AccessibleFactorization.initialRestriction d.cofibrationData
abbrev R : C ⥤ C := AccessibleFactorization.terminalRestriction d.fibrationData
abbrev q : d.Q ⟶ 𝟭 C := AccessibleFactorization.initialComparison d.cofibrationData
abbrev r : 𝟭 C ⟶ d.R := AccessibleFactorization.terminalComparison d.fibrationData

lemma Q_isCardinalAccessible : d.Q.IsCardinalAccessible κ := by
  have := d.cofibrationAccessible
  exact AccessibleFactorization.initialRestriction_isCardinalAccessible _ κ

lemma R_isCardinalAccessible : d.R.IsCardinalAccessible κ := by
  have := d.fibrationAccessible
  exact AccessibleFactorization.terminalRestriction_isCardinalAccessible _ κ

lemma Q_isCofibrant (X : C) : IsCofibrant (d.Q.obj X) :=
  AccessibleFactorization.initialRestriction_isCofibrant _ X

lemma R_isFibrant (X : C) : IsFibrant (d.R.obj X) :=
  AccessibleFactorization.terminalRestriction_isFibrant _ X

lemma q_trivialFibration (X : C) : trivialFibrations C (d.q.app X) :=
  AccessibleFactorization.initialComparison_mem _ X

lemma r_trivialCofibration (X : C) : trivialCofibrations C (d.r.app X) :=
  AccessibleFactorization.terminalComparison_mem _ X

variable [HasColimitsOfSize.{w, w} C]

lemma cofibration_left_isCardinalAccessible :
    (AccessibleFactorization.leftFactor d.cofibrationData).IsCardinalAccessible κ := by
  have := d.cofibrationAccessible
  exact AccessibleFactorization.leftFactor_isCardinalAccessible _ κ

lemma cofibration_right_isCardinalAccessible :
    (AccessibleFactorization.rightFactor d.cofibrationData).IsCardinalAccessible κ := by
  have := d.cofibrationAccessible
  exact AccessibleFactorization.rightFactor_isCardinalAccessible _ κ

lemma fibration_left_isCardinalAccessible :
    (AccessibleFactorization.leftFactor d.fibrationData).IsCardinalAccessible κ := by
  have := d.fibrationAccessible
  exact AccessibleFactorization.leftFactor_isCardinalAccessible _ κ

lemma fibration_right_isCardinalAccessible :
    (AccessibleFactorization.rightFactor d.fibrationData).IsCardinalAccessible κ := by
  have := d.fibrationAccessible
  exact AccessibleFactorization.rightFactor_isCardinalAccessible _ κ

end AccessibleModelFactorizations

lemma exists_accessible_model_factorizations [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      Nonempty (AccessibleModelFactorizations C κ) := by
  have : I.IsSmall.{w} := by
    obtain ⟨μ, hμ, hb, hI⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := I)
    exact SmallObject.isSmall I μ
  have : J.IsSmall.{w} := by
    obtain ⟨μ, hμ, hb, hJ⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := J)
    exact SmallObject.isSmall J μ
  obtain ⟨κ, hκ, dI, dJ, hI, hJ⟩ := exists_common_accessible_generated_factorizations I J
  have hcof := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J
  have htcof := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J
  have htFib := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)
  have hFib := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_J (I := I) (J := J)
  let d₁ : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C) := dI.ofLE (by rw [hcof]) (by rw [htFib])
  let d₂ : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C) := dJ.ofLE (by rw [htcof]) (by rw [hFib])
  exact ⟨κ, hκ, ⟨{
    cofibrationData := d₁
    fibrationData := d₂
    cofibrationAccessible := hI
    fibrationAccessible := hJ }⟩⟩

end SerrePositivity.Smith
