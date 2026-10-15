module

public import SerrePositivity.Spectra.General.TensorFreeAtSum
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Pushout-products of free spectra over a general coefficient category

Transport the entire pushout square and its output arrow along the actual
sum-degree free tensor comparison. No model classes are used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}
  (m n : ℕ) {A B X Y : C} (i : A ⟶ B) (j : X ⟶ Y)
  (sq : (curriedTensor C).PushoutObjObj i j)

def freePushoutProductSquare :
    (curriedTensor (GeneralSymmetricSpectrum C K)).PushoutObjObj
      ((freeAt (K := K) m).map i) ((freeAt (K := K) n).map j) where
  pt := (freeAt (K := K) (m + n)).obj sq.pt
  inl := (tensorFreeAtSum m n B X).hom ≫ (freeAt (K := K) (m + n)).map sq.inl
  inr := (tensorFreeAtSum m n A Y).hom ≫ (freeAt (K := K) (m + n)).map sq.inr
  isPushout := by
    have := (freeAtAdjunction (K := K) (m + n)).isLeftAdjoint
    refine (sq.isPushout.map (freeAt (K := K) (m + n))).of_iso
      (tensorFreeAtSum m n A X).symm
      (tensorFreeAtSum m n B X).symm
      (tensorFreeAtSum m n A Y).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · apply (cancel_epi (tensorFreeAtSum (K := K) m n A X).hom).1
      apply (cancel_mono (tensorFreeAtSum (K := K) m n B X).hom).1
      simpa [curriedTensor] using (tensorFreeAtSum_naturality (K := K) m n i (𝟙 X)).symm
    · apply (cancel_epi (tensorFreeAtSum (K := K) m n A X).hom).1
      apply (cancel_mono (tensorFreeAtSum (K := K) m n A Y).hom).1
      simpa [curriedTensor] using (tensorFreeAtSum_naturality (K := K) m n (𝟙 A) j).symm
    · simp
    · simp
  ι := (freeAt (K := K) (m + n)).map sq.ι ≫ (tensorFreeAtSum m n B Y).inv
  inl_ι := by
    apply (cancel_mono (tensorFreeAtSum (K := K) m n B Y).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Functor.map_comp, sq.inl_ι]
    simpa [curriedTensor] using (tensorFreeAtSum_naturality (K := K) m n (𝟙 B) j).symm
  inr_ι := by
    apply (cancel_mono (tensorFreeAtSum (K := K) m n B Y).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Functor.map_comp, sq.inr_ι]
    simpa [curriedTensor] using (tensorFreeAtSum_naturality (K := K) m n i (𝟙 Y)).symm

def freePushoutProductIso
    (sp : (curriedTensor (GeneralSymmetricSpectrum C K)).PushoutObjObj
      ((freeAt (K := K) m).map i) ((freeAt (K := K) n).map j)) :
    Arrow.mk sp.ι ≅ Arrow.mk ((freeAt (K := K) (m + n)).map sq.ι) := by
  let e : Arrow.mk (freePushoutProductSquare (K := K) m n i j sq).ι ≅
      Arrow.mk ((freeAt (K := K) (m + n)).map sq.ι) :=
    Arrow.isoMk (Iso.refl _) (tensorFreeAtSum m n B Y) (by
      change 𝟙 _ ≫ (freeAt (K := K) (m + n)).map sq.ι =
        ((freeAt (K := K) (m + n)).map sq.ι ≫ (tensorFreeAtSum m n B Y).inv) ≫
          (tensorFreeAtSum m n B Y).hom
      simp)
  exact (Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor (GeneralSymmetricSpectrum C K))
    (f₁ := Arrow.mk ((freeAt (K := K) m).map i))
    (f₁' := Arrow.mk ((freeAt (K := K) m).map i))
    (f₂ := Arrow.mk ((freeAt (K := K) n).map j))
    (freePushoutProductSquare (K := K) m n i j sq) sp (Iso.refl _)).symm ≪≫ e

end SerrePositivity.GeneralSymmetricSpectrum
