module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-! # Transfinite closure of localized mono equivalences in any value universe

The fixed lifting-class characterization handles limit stages, including
those of small cofinality. No value model structure or colimit preservation
by the localization functor is assumed.
-/

@[expose] public section
universe w v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanLocalizedTransfinite
open KanTestLiftingClass

lemma stableOfShape (J : Type v) [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] : localizedMonos.{v}.IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    rintro A B f ⟨d⟩
    have hm : (MorphismProperty.monomorphisms SSet.{v}).transfiniteCompositionsOfShape J f :=
      ⟨d.ofLE (fun _ _ _ h => h.1)⟩
    have hl : rightTests.llp.transfiniteCompositionsOfShape J f :=
      ⟨d.ofLE localizedMono_le_llp⟩
    exact ⟨(MorphismProperty.monomorphisms SSet.{v}).transfiniteCompositionsOfShape_le J f hm,
      localized_isIso_of_llp f (rightTests.llp.transfiniteCompositionsOfShape_le J f hl)⟩

instance stableSmallOfShape (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] :
    localizedMonos.{v}.IsStableUnderTransfiniteCompositionOfShape J :=
  (MorphismProperty.isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso
    localizedMonos (orderIsoShrink.{v} J)).mpr (stableOfShape _)

instance stable : MorphismProperty.IsStableUnderTransfiniteComposition.{v} localizedMonos.{v} where

lemma localized_isIso (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] {A B : SSet.{v}} (f : A ⟶ B)
    (d : localizedMonos.TransfiniteCompositionOfShape J f) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) :=
  (localizedMonos.transfiniteCompositionsOfShape_le J f ⟨d⟩).2

lemma image_isIso (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] {A B : SSet.{v}} (f : A ⟶ B)
    (d : localizedMonos.TransfiniteCompositionOfShape J f)
    {D : Type uH} [Category.{vH} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map f) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL f (localized_isIso J f d)

lemma cocone_mem (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] (F : J ⥤ SSet.{v}) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬IsMax j → localizedMonos (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : localizedMonos (c.ι.app ⊥) := by
  let d : localizedMonos.TransfiniteCompositionOfShape J (c.ι.app ⊥) :=
    { F := F, isoBot := Iso.refl _, incl := c.ι, isColimit := hc, map_mem := hF }
  exact localizedMonos.transfiniteCompositionsOfShape_le J _ ⟨d⟩

lemma sequential_cocone_mem (F : ℕ ⥤ SSet.{v})
    (hF : ∀ n, localizedMonos (F.map (homOfLE (Nat.le_succ n))))
    (c : Cocone F) (hc : IsColimit c) : localizedMonos (c.ι.app 0) :=
  cocone_mem ℕ F (fun n _ => hF n) c hc

end SerrePositivity.SimplicialModel.KanLocalizedTransfinite
