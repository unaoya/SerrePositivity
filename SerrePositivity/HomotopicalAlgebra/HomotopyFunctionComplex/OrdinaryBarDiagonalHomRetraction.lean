module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # An explicit all-degree Hom retraction without a large simplicial model structure -/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction
open OrdinaryBarFreeResolutionSeed OrdinaryBarFixedWordResolution OrdinaryBarDiagonalAmbientHom
variable (C : Type u) [Category.{v} C]

def sandwich (X Y : D C) : ambientHom C X Y ⊗ WordSegment.interval ⟶ ambientHom C X Y where
  app n := ↾fun x => wordAt C n X (WordSegment.letter.app n x.2) ≫ x.1 ≫
    wordAt C n Y (WordSegment.letter.app n x.2)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    change wordAt C m X (WordSegment.letter.app m (WordSegment.interval.map θ x.2)) ≫
      ((diagram C).map θ).toFunctor.map x.1 ≫
        wordAt C m Y (WordSegment.letter.app m (WordSegment.interval.map θ x.2)) =
          ((diagram C).map θ).toFunctor.map
            (wordAt C n X (WordSegment.letter.app n x.2) ≫ x.1 ≫
              wordAt C n Y (WordSegment.letter.app n x.2))
    rw [Functor.map_comp, Functor.map_comp, map_word, map_word]
    have h := types_congr_hom (WordSegment.letter.naturality θ) x.2
    change WordSegment.letter.app _ (WordSegment.interval.map θ x.2) =
      WordSegment.degreeMap θ (WordSegment.letter.app _ x.2) at h
    rw [h]

def contraction (X Y : D C) :
    SSet.Homotopy (𝟙 (ambientHom C X Y)) (transfer C X Y ≫ inclusion C X Y) where
  h := sandwich C X Y
  h₀ := by
    ext n f
    change wordAt C n X (WordSegment.letter.app n (WordSegment.endpoint n 0)) ≫ f ≫
      wordAt C n Y (WordSegment.letter.app n (WordSegment.endpoint n 0)) = f
    rw [WordSegment.letter_unit, wordAt, wordAt, RetractWords.quotient_word_one,
      RetractWords.quotient_word_one, Category.id_comp, Category.comp_id]
  h₁ := by
    ext n f
    change wordAt C n X (WordSegment.letter.app n (WordSegment.endpoint n 1)) ≫ f ≫
      wordAt C n Y (WordSegment.letter.app n (WordSegment.endpoint n 1)) =
        projectionAt C n X ≫ (sectionAt C n X ≫ f ≫ projectionAt C n Y) ≫ sectionAt C n Y
    rw [WordSegment.letter_zero, wordAt, wordAt, RetractWords.quotient_word_zero,
      RetractWords.quotient_word_zero]
    simp only [Category.assoc]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
def comparisonIso (X Y : D C) : L.obj (ambientHom C X Y) ≅ L.obj (hom C X Y) :=
  AnodyneHomotopy.mapRetractionIso L hL (transfer C X Y) (inclusion C X Y)
    (inclusion_transfer C X Y) (contraction C X Y)

lemma localized_transfer_isIso (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (transfer C X Y)) :=
  (comparisonIso C AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) X Y).isIso_hom

lemma localized_inclusion_isIso (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (inclusion C X Y)) :=
  (comparisonIso C AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) X Y).isIso_inv

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction
