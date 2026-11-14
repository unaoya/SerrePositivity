module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Smith.GeneratedWeakReflection

/-! # Accessibility of a small generated right lifting class

A0 supplies an accessible weak reflection. Uniformization supplies preservation
of presentable objects. The resulting bounded weak reflection constructs a
small generating family for the original full right lifting subcategory.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.AccessibleRightClass
variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
  [∀ i : I.toSet, IsCardinalPresentable i.val.right κ]

include I in
lemma hasCardinalFilteredColimits :
    HasCardinalFilteredColimits.{w} (arrowProperty I.rlp).FullSubcategory κ where
  hasColimitsOfShape J _ _ := by
    have := AccessibleLiftingClosure.closedUnderColimitsOfShape I κ (J := J)
    infer_instance

lemma inclusion_isCardinalAccessible : (arrowInclusion I.rlp).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := AccessibleLiftingClosure.closedUnderColimitsOfShape I κ (J := J)
    infer_instance

lemma isCardinalAccessibleCategory [IsCardinalLocallyPresentable (Arrow C) κ]
    (d : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp)
    [(GeneratedWeakReflection.rightFactor I d).PreservesCardinalPresentable κ] :
    IsCardinalAccessibleCategory (arrowProperty I.rlp).FullSubcategory κ := by
  have := hasCardinalFilteredColimits I κ
  have := inclusion_isCardinalAccessible I κ
  exact (GeneratedWeakReflection.presentableReflection I d κ).isCardinalAccessibleCategory

end SerrePositivity.Smith.AccessibleRightClass

namespace SerrePositivity.Smith

lemma exists_accessible_right_lifting_class
    {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
    (I : MorphismProperty C) [I.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (arrowProperty I.rlp).FullSubcategory κ ∧
      (arrowInclusion I.rlp).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := C)
  obtain ⟨κa, ha, d, _, hd, _⟩ := exists_common_accessible_generated_factorizations I I
  have : d.Z.IsCardinalAccessible κa := hd
  let R := GeneratedWeakReflection.rightFactor I d
  have : R.IsCardinalAccessible κa := AccessibleFactorization.rightFactor_isCardinalAccessible d κa
  have : R.IsAccessible.{w} := R.isAccessible_of_isCardinalAccessible κa
  obtain ⟨κ₁, h₁, hA, _, hR, hRp⟩ := IsCardinalAccessibleCategory.uniformization R
  obtain ⟨κ₀, h₀, hp⟩ := exists_common_arrow_presentability (fun i : I.toSet ↦ i.val)
  obtain ⟨κ, hκ, hκ₀, hκ₁⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κ₁
  have := hκ₁.isCardinalAccessibleCategory (Arrow C)
  have : IsCardinalLocallyPresentable (Arrow C) κ := {}
  have : R.PreservesCardinalPresentable κ :=
    IsCardinalAccessibleCategory.uniformization_aux R hκ₁ (by
    intro X hX
    have : IsCardinalPresentable X κ₁ := hX
    have : IsCardinalPresentable (R.obj X) κ₁ := inferInstance
    exact isCardinalPresentable_of_le _ hκ₁.le)
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.left κ := fun i ↦ by
    have := (hp i).1
    exact isCardinalPresentable_of_le _ hκ₀.le
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.right κ := fun i ↦ by
    have := (hp i).2
    exact isCardinalPresentable_of_le _ hκ₀.le
  exact ⟨κ, hκ, AccessibleRightClass.isCardinalAccessibleCategory I κ d,
    AccessibleRightClass.inclusion_isCardinalAccessible I κ⟩

end SerrePositivity.Smith

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.6.8" (partial := stronger-hyp) "仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と小さい生成 I,J の CofibrantlyGenerated（Lean の形式的仮定が強い）。結論：元の W の full arrow subcategory と inclusion が accessible、F=J.rlp と F∩W=I.rlp も同じ right-lifting-class theorem により accessible となり、原典の三結論に一致。HTT の可呈示性と生成の定義から入力を得る完全な比較は未供給。"] _root_.SerrePositivity.Smith.exists_accessible_right_lifting_class
