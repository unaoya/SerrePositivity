module

public import SerrePositivity.Spectra.SymmetricSpectrum.Basic
public import SerrePositivity.Spectra.General.TensorClosed
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Pushout-products of free simplicial spectra

The free tensor comparison transports the entire pushout square, including
its output map. This is a categorical calculation independent of all model
classes and literature inputs.
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (tensorFreeAtSum_naturality)
open PointedSimplicialSet (circle)

variable (m n : ℕ) {A B X Y : PointedSimplicialSet.{u}} (i : A ⟶ B) (j : X ⟶ Y)
  (sq : (curriedTensor PointedSimplicialSet.{u}).PushoutObjObj i j)

/-- A free image of the source pushout-product is the actual spectrum
pushout-product of the two free arrows, after the tensor comparison. -/
def freePushoutProductSquare : (curriedTensor SymmetricSpectrum.{u}).PushoutObjObj
    ((freeAt m).map i) ((freeAt n).map j) where
  pt := (freeAt (m + n)).obj sq.pt
  inl := (sphereTensorFreeAtSum m n B X).hom ≫ (freeAt (m + n)).map sq.inl
  inr := (sphereTensorFreeAtSum m n A Y).hom ≫ (freeAt (m + n)).map sq.inr
  isPushout := by
    let : (freeAt.{u} (m + n)).IsLeftAdjoint := (freeAtAdjunction (m + n)).isLeftAdjoint
    refine (sq.isPushout.map (freeAt (m + n))).of_iso
      (sphereTensorFreeAtSum m n A X).symm
      (sphereTensorFreeAtSum m n B X).symm
      (sphereTensorFreeAtSum m n A Y).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · apply (cancel_epi (sphereTensorFreeAtSum m n A X).hom).1
      apply (cancel_mono (sphereTensorFreeAtSum m n B X).hom).1
      simpa using
        (tensorFreeAtSum_naturality (K := circle) m n i (𝟙 X)).symm
    · apply (cancel_epi (sphereTensorFreeAtSum m n A X).hom).1
      apply (cancel_mono (sphereTensorFreeAtSum m n A Y).hom).1
      simpa using
        (tensorFreeAtSum_naturality (K := circle) m n (𝟙 A) j).symm
    · simp
    · simp
  ι := (freeAt (m + n)).map sq.ι ≫ (sphereTensorFreeAtSum m n B Y).inv
  inl_ι := by
    apply (cancel_mono (sphereTensorFreeAtSum m n B Y).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← (freeAt (m + n)).map_comp, sq.inl_ι]
    simpa using
      (tensorFreeAtSum_naturality (K := circle) m n (𝟙 B) j).symm
  inr_ι := by
    apply (cancel_mono (sphereTensorFreeAtSum m n B Y).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← (freeAt (m + n)).map_comp, sq.inr_ι]
    simpa using
      (tensorFreeAtSum_naturality (K := circle) m n i (𝟙 Y)).symm

/-- Compare an arbitrary spectrum pushout choice with the free image of an
arbitrary pointed pushout choice, as an isomorphism of actual arrows. -/
def freePushoutProductIso
    (sp : (curriedTensor SymmetricSpectrum.{u}).PushoutObjObj
      ((freeAt m).map i) ((freeAt n).map j)) :
    Arrow.mk sp.ι ≅ Arrow.mk ((freeAt (m + n)).map sq.ι) := by
  let e : Arrow.mk (freePushoutProductSquare m n i j sq).ι ≅
      Arrow.mk ((freeAt (m + n)).map sq.ι) :=
    Arrow.isoMk (Iso.refl _) (sphereTensorFreeAtSum m n B Y) (by
      change 𝟙 _ ≫ (freeAt (m + n)).map sq.ι =
        ((freeAt (m + n)).map sq.ι ≫ (sphereTensorFreeAtSum m n B Y).inv) ≫
          (sphereTensorFreeAtSum m n B Y).hom
      simp)
  exact (Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SymmetricSpectrum.{u}) (f₁ := Arrow.mk ((freeAt m).map i))
    (f₁' := Arrow.mk ((freeAt m).map i)) (f₂ := Arrow.mk ((freeAt n).map j))
    (freePushoutProductSquare m n i j sq) sp (Iso.refl _)).symm ≪≫ e

end SerrePositivity.SymmetricSpectrum
