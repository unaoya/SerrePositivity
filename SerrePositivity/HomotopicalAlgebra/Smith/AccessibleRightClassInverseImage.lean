module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Smith.RightClassInverseImageCover
public import SerrePositivity.HomotopicalAlgebra.Smith.GeneratedWeakReflection

/-! # Accessible inverse images of small generated right classes

This is a proved closure operation with local presentable covers. It does not
assert accessibility of arbitrary full images of accessible functors.
-/

@[expose] public section
universe w v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith

lemma exists_accessible_rightClass_inverseImage
    {C : Type u₁} [Category.{v₁} C] [IsLocallyPresentable.{w} C]
    {E : Type u₂} [Category.{v₂} E] [IsLocallyPresentable.{w} E]
    (I : MorphismProperty E) [I.IsSmall.{w}]
    (F : C ⥤ Arrow E) [F.IsAccessible.{w}] :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular),
      IsCardinalAccessibleCategory ((arrowProperty I.rlp).inverseImage F).FullSubcategory ν ∧
      (((arrowProperty I.rlp).inverseImage F).ι).IsCardinalAccessible ν := by
  have := locallyPresentable_hasColimits (C := C)
  have := locallyPresentable_hasColimits (C := E)
  obtain ⟨κa, ha, d, _, hd, _⟩ := exists_common_accessible_generated_factorizations I I
  have : d.Z.IsCardinalAccessible κa := hd
  let R := GeneratedWeakReflection.rightFactor I d
  have : R.IsCardinalAccessible κa := AccessibleFactorization.rightFactor_isCardinalAccessible d κa
  have : R.IsAccessible.{w} := R.isAccessible_of_isCardinalAccessible κa
  obtain ⟨κ₁, h₁, hC, hE, _, _, hF, hR, hFp, hRp⟩ :=
    IsCardinalAccessibleCategory.uniformization_pair F R
  obtain ⟨κ₀, h₀, hp⟩ := exists_common_arrow_presentability (fun i : I.toSet ↦ i.val)
  let μ := max κ₁ κ₀
  have : Fact μ.IsRegular := ⟨by
    rcases le_total κ₁ κ₀ with h | h
    · simpa only [μ, max_eq_right h] using h₀.out
    · simpa only [μ, max_eq_left h] using h₁.out⟩
  have : F.IsCardinalAccessible μ := F.isCardinalAccessible_of_le (le_max_left _ _)
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.left μ := fun i ↦ by
    have := (hp i).1
    exact isCardinalPresentable_of_le _ (le_max_right _ _)
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.right μ := fun i ↦ by
    have := (hp i).2
    exact isCardinalPresentable_of_le _ (le_max_right _ _)
  obtain ⟨ν, hν, hμν, h₁ν⟩ := Cardinal.SharplyLT.exists_of_pair μ κ₁
  have := h₁ν.isCardinalAccessibleCategory C
  have := h₁ν.isCardinalAccessibleCategory (Arrow E)
  have : F.IsCardinalAccessible ν := F.isCardinalAccessible_of_le h₁ν.le
  have : F.PreservesCardinalPresentable ν :=
    IsCardinalAccessibleCategory.uniformization_aux F h₁ν (by
      intro X hX
      have : IsCardinalPresentable X κ₁ := hX
      have : IsCardinalPresentable (F.obj X) κ₁ := inferInstance
      exact isCardinalPresentable_of_le _ h₁ν.le)
  have : R.PreservesCardinalPresentable ν :=
    IsCardinalAccessibleCategory.uniformization_aux R h₁ν (by
      intro X hX
      have : IsCardinalPresentable X κ₁ := hX
      have : IsCardinalPresentable (R.obj X) κ₁ := inferInstance
      exact isCardinalPresentable_of_le _ h₁ν.le)
  have : Nonempty μ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : μ.IsRegular).ne_zero
  have : OrderBot μ.ord.ToType := WellFoundedLT.toOrderBot _
  let P := (arrowProperty I.rlp).inverseImage F
  have hcover : LocalPresentableCover P ν := rightClass_inverseImage_localCover I μ ν hμν.lt F
    (GeneratedWeakReflection.presentableReflection I d ν)
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.left ν := fun i ↦
    isCardinalPresentable_of_le _ hμν.le
  have : ∀ i : I.toSet, IsCardinalPresentable i.val.right ν := fun i ↦
    isCardinalPresentable_of_le _ hμν.le
  have hclosed (J : Type w) [SmallCategory J] [IsCardinalFiltered J ν] :
      P.IsClosedUnderColimitsOfShape J := by
    have := AccessibleLiftingClosure.closedUnderColimitsOfShape I ν (J := J)
    have := F.preservesColimitsOfShape_of_isCardinalAccessible ν J
    infer_instance
  have : HasCardinalFilteredColimits.{w} P.FullSubcategory ν :=
    { hasColimitsOfShape J _ _ := by have := hclosed J; infer_instance }
  have : P.ι.IsCardinalAccessible ν :=
    { preservesColimitOfShape J _ _ := by have := hclosed J; infer_instance }
  exact ⟨ν, hν, hcover.isCardinalAccessibleCategory, inferInstance⟩

end SerrePositivity.Smith

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.6.7" (partial := component) "仮定：C は Mathlib locally presentable、D=Arrow(E)、E も locally presentable、D0 は小さい生成射 I に対する right lifting class I.rlp、F:C→Arrow(E) は accessible（原典より特殊）。結論：F⁻¹D0 とその包含はある正則 ν で accessible。原典の固定した κ での κ-accessibility より弱く、一般の D0 も含まないが、この inverse-image category そのものの accessibility の部分は直接得られる。"] _root_.SerrePositivity.Smith.exists_accessible_rightClass_inverseImage
