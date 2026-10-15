module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleModelFactorizations
public import SerrePositivity.HomotopicalAlgebra.Smith.SolutionSet
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-! # Filtered-colimit closure of a generated right lifting class

A square out of a presentable generating arrow factors through one stage of
the filtered diagram. A lift at that stage gives a lift in its colimit.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.AccessibleLiftingClosure
variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
  [∀ i : I.toSet, IsCardinalPresentable i.val.right κ]
  {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]

include κ

lemma rlp_of_isColimit {F : J ⥤ Arrow C} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, I.rlp (F.obj j).hom) : I.rlp c.pt.hom := by
  intro A B i hi
  apply (Arrow.hasLiftingProperty_iff i c.pt.hom).2
  intro φ
  have : IsCardinalPresentable A κ := inferInstanceAs
    (IsCardinalPresentable (⟨Arrow.mk i, hi⟩ : I.toSet).val.left κ)
  have : IsCardinalPresentable B κ := inferInstanceAs
    (IsCardinalPresentable (⟨Arrow.mk i, hi⟩ : I.toSet).val.right κ)
  have : IsCardinalPresentable (Arrow.mk i) κ :=
    Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) i
  obtain ⟨j, ψ, hψ⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc φ
  obtain ⟨l⟩ := (Arrow.hasLiftingProperty_iff i (F.obj j).hom).1 (hF j i hi) ψ
  refine ⟨{ l := l.l ≫ (c.ι.app j).left, fac_left := ?_, fac_right := ?_ }⟩
  · rw [← Category.assoc, l.fac_left]
    exact congrArg Arrow.Hom.left hψ
  · change (l.l ≫ (c.ι.app j).left) ≫ c.pt.hom = φ.right
    calc
      _ = l.l ≫ ((c.ι.app j).left ≫ c.pt.hom) := Category.assoc _ _ _
      _ = l.l ≫ ((F.obj j).hom ≫ (c.ι.app j).right) :=
        congrArg (fun k ↦ l.l ≫ k) (c.ι.app j).w
      _ = (l.l ≫ (F.obj j).hom) ≫ (c.ι.app j).right := (Category.assoc _ _ _).symm
      _ = ψ.right ≫ (c.ι.app j).right := congrArg (fun k ↦ k ≫ (c.ι.app j).right) l.fac_right
      _ = φ.right := congrArg Arrow.Hom.right hψ

lemma closedUnderColimitsOfShape :
    (arrowProperty I.rlp).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le X hX := by
    obtain ⟨h⟩ := hX
    exact rlp_of_isColimit I κ h.isColimit h.prop_diag_obj

end SerrePositivity.Smith.AccessibleLiftingClosure
