module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleRightClassInverseImage
public import SerrePositivity.HomotopicalAlgebra.Smith.WeakEquivalenceFilteredColimits

/-! # Accessibility of the original weak equivalences in a combinatorial model

The second generated model factorization detects the original weak
equivalences by membership of its right factor in I.rlp. Accessibility follows
from the proved inverse-image theorem, including its small generating family.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C]

lemma arrow_locallyPresentable [IsLocallyPresentable.{w} C] :
    IsLocallyPresentable.{w} (Arrow C) := by
  have := locallyPresentable_hasColimits (C := C)
  obtain ⟨κ, hκ, hA⟩ := IsAccessibleCategory.exists_cardinal.{w} (Arrow C)
  exact ⟨κ, hκ, { }⟩

variable [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I J

lemma exists_accessible_weakEquivalences :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
      (arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := C)
  have := arrow_locallyPresentable (C := C)
  have : I.IsSmall.{w} := by
    obtain ⟨μ, hμ, hb, hI⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := I)
    exact SmallObject.isSmall I μ
  obtain ⟨κ₀, h₀, ⟨d⟩⟩ := exists_accessible_model_factorizations C I J
  have := d.fibrationAccessible
  let F := AccessibleFactorization.rightFactor d.fibrationData
  have : F.IsCardinalAccessible κ₀ :=
    AccessibleFactorization.rightFactor_isCardinalAccessible d.fibrationData κ₀
  have : F.IsAccessible.{w} := F.isAccessible_of_isCardinalAccessible κ₀
  have h := exists_accessible_rightClass_inverseImage I F
  have hI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)
  rw [← WeakEquivalenceFilteredColimits.arrowProperty_eq_inverseImage d.fibrationData I hI] at h
  exact h

lemma weakEquivalences_isAccessibleCategory :
    IsAccessibleCategory.{w} (arrowProperty (weakEquivalences C)).FullSubcategory := by
  obtain ⟨κ, hκ, hW, _⟩ := exists_accessible_weakEquivalences I J
  exact ⟨κ, hκ, hW⟩

lemma weakEquivalences_inclusion_isAccessible :
    (arrowInclusion (weakEquivalences C)).IsAccessible.{w} := by
  obtain ⟨κ, hκ, _, hW⟩ := exists_accessible_weakEquivalences I J
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

/-- A0 and A1 hold simultaneously at a common sufficiently large regular
cardinal, using the specified accessible model factorizations. -/
lemma exists_accessible_model_and_weakEquivalences :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ _d : AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory (arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ := by
  obtain ⟨κ₀, h₀, ⟨d⟩⟩ := exists_accessible_model_factorizations C I J
  obtain ⟨κ₁, h₁, hW, hι⟩ := exists_accessible_weakEquivalences I J
  obtain ⟨κ, hκ, hκ₀, hκ₁⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κ₁
  exact ⟨κ, hκ, d.atLarger κ hκ₀.le,
    hκ₁.isCardinalAccessibleCategory _,
    Functor.isCardinalAccessible_of_le _ hκ₁.le⟩

lemma weakEquivalences_solutionSetCondition :
    SolutionSetCondition.{w} (arrowInclusion (weakEquivalences C)) := by
  have := weakEquivalences_isAccessibleCategory I J
  have := weakEquivalences_inclusion_isAccessible I J
  exact solutionSetCondition (weakEquivalences C)

end SerrePositivity.Smith

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.6.11" (partial := stronger-hyp) "仮定：抽象モデル圏 C が Mathlib locally presentable、I は small cofibration generators、W の可到達性は intrinsic accessible category と accessible inclusion を持つ形式（Lean の形式的仮定が強い）。結論：既存の combinatorial generation から元の W の accessibility、逆にその W の入力から同じモデル圏の small trivial-cofibration generators を構成する二方向が一致。原典の可呈示性・accessible full subcategory の定義からの入力比較は未供給。"] _root_.SerrePositivity.Smith.exists_accessible_weakEquivalences
attribute [cite HTT "A.2.6.8" (partial := stronger-hyp) "仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と小さい生成 I,J の CofibrantlyGenerated（Lean の形式的仮定が強い）。結論：元の W の full arrow subcategory と inclusion が accessible、F=J.rlp と F∩W=I.rlp も同じ right-lifting-class theorem により accessible となり、原典の三結論に一致。HTT の可呈示性と生成の定義から入力を得る完全な比較は未供給。"] _root_.SerrePositivity.Smith.exists_accessible_weakEquivalences
