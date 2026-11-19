module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorMapLevels
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorCurryNaturality
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorMapLevels
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorLevelEvaluation

/-! # 両変数のテンソル・スペクトル射の各段のsmashの法則 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 値域の恒等射を使うcotensorの射は生成対象の前合成。 -/
lemma cotensorMap_id {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) : cotensorMap f (𝟙 E) = cotensorPre f E := by
  unfold cotensorMap
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- cotensorの前合成の各段の通常の内部Homの法則。 -/
def cotensorPreLevelLaw {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) (q : ℕ) : Prop :=
  SymmetricSequence.unshiftedInternalHomMapLevelLaw f (𝟙 E.X)
    ((Iso.refl (cotensor Y E).X).inv ≫ (cotensorPre f E).hom ≫
      (Iso.refl (cotensor X E).X).hom) q

/-- cotensorの前合成は各段の通常の内部Homの前合成になる。 -/
lemma cotensorPre_level {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) (q : ℕ) : cotensorPreLevelLaw f E q := by
  have h := cotensorMap_app q f (𝟙 E)
  unfold cotensorMapLevelLaw at h
  rw [cotensorMap_id] at h
  exact h

end SerrePositivity.SymmetricSpectrum
