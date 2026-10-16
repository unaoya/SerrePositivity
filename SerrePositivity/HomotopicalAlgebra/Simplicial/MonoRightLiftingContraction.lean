module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRelativeLifting

/-! # All-monomorphism right lifting gives a strict section and a vertical contraction

The original map need not have Kan source or target. The contraction is
filled over the original base, using only the interval boundary mono.
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.MonoRightLiftingContraction
variable {E B : SSet.{v}} (p : E ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)

include hp in
lemma exists_section : ∃ s : B ⟶ E, s ≫ p = 𝟙 B := by
  have : HasLiftingProperty (initial.to B) p := hp _ inferInstance
  let sq : CommSq (initial.to E) (initial.to B) p (𝟙 B) := ⟨initial.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

include hp in
lemma exists_vertical_contraction (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) :
    ∃ H : SSet.Homotopy (𝟙 E) (p ≫ s),
      H.h ≫ p = fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p := by
  let b := LargeParameterHomotopy.boundaryMap (𝟙 E) (p ≫ s)
  let q := fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p
  have hw : b ≫ p = E ◁ (SSet.boundary 1).ι ≫ q := by
    apply (LargeParameterHomotopy.boundaryColimit E).hom_ext
    rintro ⟨j⟩
    cases j
    · change (E ◁ SSet.boundary.ι (1 : Fin 2)) ≫ (b ≫ p) =
        (E ◁ SSet.boundary.ι (1 : Fin 2)) ≫ (E ◁ (SSet.boundary 1).ι ≫ q)
      dsimp only [b, q]
      rw [← Category.assoc, LargeParameterHomotopy.boundaryMap_zero, Category.comp_id]
      conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
        SSet.stdSimplex.δ_one_eq_const]
      rfl
    · change (E ◁ SSet.boundary.ι (0 : Fin 2)) ≫ (b ≫ p) =
        (E ◁ SSet.boundary.ι (0 : Fin 2)) ≫ (E ◁ (SSet.boundary 1).ι ≫ q)
      dsimp only [b, q]
      rw [← Category.assoc, LargeParameterHomotopy.boundaryMap_one]
      conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
        SSet.stdSimplex.δ_zero_eq_const]
      simp only [Category.assoc, hs, Category.comp_id]
      rfl
  have : HasLiftingProperty (E ◁ (SSet.boundary 1).ι) p := hp _ inferInstance
  let sq : CommSq b (E ◁ (SSet.boundary 1).ι) p q := ⟨hw⟩
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }, sq.fac_right⟩
  · change SSet.ι₀ ≫ sq.lift = 𝟙 E
    rw [← LargeParameterHomotopy.section_zero E, Category.assoc,
      ← SSet.boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, sq.fac_left]
    dsimp only [b]
    rw [LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change SSet.ι₁ ≫ sq.lift = p ≫ s
    rw [← LargeParameterHomotopy.section_one E, Category.assoc,
      ← SSet.boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, sq.fac_left]
    dsimp only [b]
    rw [LargeParameterHomotopy.boundaryMap_one]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

include hp in
lemma image_isIso {D : Type uH} [Category.{vH} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map p) := by
  obtain ⟨s, hs⟩ := exists_section p hp
  obtain ⟨H, _⟩ := exists_vertical_contraction p hp s hs
  exact (AnodyneHomotopy.mapRetractionIso L hL p s hs H).isIso_hom

include hp in
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map p) :=
  image_isIso p hp AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)

end SerrePositivity.SimplicialModel.MonoRightLiftingContraction
