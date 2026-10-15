module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLiftingClosure

/-! # Lifts in filtered colimits with eventually good transitions

The stages need not be in the right class: it suffices that each stage has a
later transition factoring through an object of the right class.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.LiftingColimitRefinement
variable {C : Type u} [Category.{v} C]

def postcomposeLift {i p q : Arrow C} {ψ : i ⟶ p}
    (l : Arrow.LiftStruct ψ) (δ : p ⟶ q) : Arrow.LiftStruct (ψ ≫ δ) where
  l := l.l ≫ δ.left
  fac_left := by
    change i.hom ≫ (l.l ≫ δ.left) = ψ.left ≫ δ.left
    rw [← Category.assoc, l.fac_left]
  fac_right := by
    change (l.l ≫ δ.left) ≫ q.hom = ψ.right ≫ δ.right
    calc
      _ = l.l ≫ (δ.left ≫ q.hom) := Category.assoc _ _ _
      _ = l.l ≫ (p.hom ≫ δ.right) := congrArg (fun a ↦ l.l ≫ a) δ.w
      _ = (l.l ≫ p.hom) ≫ δ.right := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun a ↦ a ≫ δ.right) l.fac_right

variable [HasColimitsOfSize.{w, w} C] (I : MorphismProperty C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
  [∀ i : I.toSet, IsCardinalPresentable i.val.right κ]
  {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]

include κ in
lemma rlp_of_factorizing_transitions {F : J ⥤ Arrow C} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, ∃ (k : J) (a : j ⟶ k) (p : Arrow C) (_ : I.rlp p.hom)
      (α : F.obj j ⟶ p) (β : p ⟶ F.obj k), α ≫ β = F.map a) : I.rlp c.pt.hom := by
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
  obtain ⟨k, a, p, hp, α, β, hαβ⟩ := hF j
  obtain ⟨l⟩ := (Arrow.hasLiftingProperty_iff i p.hom).1 (hp i hi) (ψ ≫ α)
  have hcomp : (ψ ≫ α) ≫ (β ≫ c.ι.app k) = φ := by
    rw [Category.assoc, ← Category.assoc α β, hαβ, c.w a]
    exact hψ
  exact ⟨hcomp ▸ postcomposeLift l (β ≫ c.ι.app k)⟩

end SerrePositivity.Smith.LiftingColimitRefinement
