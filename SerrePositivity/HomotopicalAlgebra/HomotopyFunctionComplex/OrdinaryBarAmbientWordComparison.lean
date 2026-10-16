module

public import SerrePositivity.CategoryTheory.Presentation.AmbientWordMap
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation

/-! # The actual diagonal ambient Hom as a presentation without split vertices -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarDiagonalAmbientHom
variable (C : Type u) [Category.{v} C]

abbrev degreeEquiv (n : SimplexCategoryᵒᵖ) (X Y : D C) :=
  AmbientWords.ambientHomEquiv (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n) X Y

def hom (X Y : D C) : SSet.{max u v} where
  obj n := (AmbientWords.sourceFunctor (degree (D C) (n.unop.len + 1))
      (WordSegment.degree.{max u v} n)).obj X ⟶
    (AmbientWords.sourceFunctor (degree (D C) (n.unop.len + 1))
      (WordSegment.degree.{max u v} n)).obj Y
  map {n m} θ := ↾fun f => (degreeEquiv C m X Y).symm
    ((ambientHom C X Y).map θ (degreeEquiv C n X Y f))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    change (degreeEquiv C n X Y).symm
      ((ambientHom C X Y).map (𝟙 n) (degreeEquiv C n X Y f)) = f
    rw [types_congr_hom ((ambientHom C X Y).map_id n)]
    exact (degreeEquiv C n X Y).symm_apply_apply f
  map_comp {a b c} θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    change (degreeEquiv C c X Y).symm
      ((ambientHom C X Y).map (θ ≫ φ) (degreeEquiv C a X Y f)) = _
    rw [types_congr_hom ((ambientHom C X Y).map_comp θ φ)]
    dsimp
    rw [Equiv.apply_symm_apply]

def comparisonIso (X Y : D C) : hom C X Y ≅ ambientHom C X Y :=
  NatIso.ofComponents (fun n => Equiv.toIso (degreeEquiv C n X Y)) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    exact (degreeEquiv C m X Y).apply_symm_apply _)

lemma map_eq {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {X Y : D C}
    (f : (hom C X Y).obj n) :
    (hom C X Y).map θ f =
      (AmbientWords.map (OrdinaryBarFixedSource.literalMap C θ)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n)) ⋙
      AmbientWords.map (𝟭 (degree (D C) (m.unop.len + 1))) (WordSegment.degreeMap θ)).map f := by
  apply (degreeEquiv C m X Y).injective
  change (degreeEquiv C m X Y) ((degreeEquiv C m X Y).symm _) = _
  rw [Equiv.apply_symm_apply]
  have h := congr($(AmbientWords.map_toRetract
    (OrdinaryBarFixedSource.literalMap C θ)
    (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n))).map f)
  have k := congr($(AmbientWords.map_toRetract
    (𝟭 (degree (D C) (m.unop.len + 1))) (WordSegment.degreeMap θ)).map
      ((AmbientWords.map (OrdinaryBarFixedSource.literalMap C θ)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n))).map f))
  exact (k.trans (congrArg
    (fun g => (RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1)))
      (WordSegment.degreeMap θ)).map g) h)).symm

def augmentation (X Y : D C) : hom C X Y ⟶
    OrdinaryBarDiagonalHomAugmentation.baseHom C X Y :=
  (comparisonIso C X Y).hom ≫ OrdinaryBarDiagonalHomAugmentation.ambientAugmentation C X Y

lemma localized_small_iff_words (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) ↔
        IsIso (AnodyneHomotopy.anodyneQ.map (augmentation C X Y)) := by
  rw [augmentation, Functor.map_comp]
  have : IsIso (AnodyneHomotopy.anodyneQ.map (comparisonIso C X Y).hom) := inferInstance
  rw [isIso_comp_left_iff]
  exact OrdinaryBarDiagonalHomAugmentation.localized_small_iff_ambient C X Y

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison
