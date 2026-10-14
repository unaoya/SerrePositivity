module

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

/-- テンソルの生成対象の射の各段の通常のsmashの法則。 -/
def pointwiseTensorPostLevelLaw {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (A : SymmetricSpectrum.{u}) (q : ℕ) : Prop :=
  SymmetricSequence.pointwiseTensorPostModuleLevelLaw sphereSequence.{u} f A
    (pointwiseTensorPost f A) q

/-- 生成対象の射は各段の通常のsmashの射になる。 -/
lemma pointwiseTensorPost_level {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (A : SymmetricSpectrum.{u}) (q : ℕ) : pointwiseTensorPostLevelLaw f A q := by
  apply SymmetricSequence.pointwiseTensorPostModuleLevelLaw_of_curry sphereSequence.{u} f A
    (Iso.refl (cotensor Y (pointwiseTensor Y A)).X)
    (Iso.refl (cotensor X (pointwiseTensor Y A)).X)
    (pointwiseTensorCurry Y (𝟙 (pointwiseTensor Y A)))
    (cotensorPre f (pointwiseTensor Y A))
  · exact pointwiseTensorCurry_level Y (𝟙 (pointwiseTensor Y A)) q
  · exact cotensorPre_level f (pointwiseTensor Y A) q
  · have h := pointwiseTensorUncurry_level X
      (pointwiseTensorCurry Y (𝟙 (pointwiseTensor Y A)) ≫
        cotensorPre f (pointwiseTensor Y A)) q
    unfold pointwiseTensorUncurryLevelLaw at h
    rw [pointwiseTensorUncurry_pre, pointwiseTensorUncurry_curry, Category.comp_id] at h
    exact h

/-- 両変数のテンソル射の各段の通常のsmashの法則。 -/
def pointwiseTensorBimapLevelLaw {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {A B : SymmetricSpectrum.{u}} (g : A ⟶ B) (q : ℕ) : Prop :=
  SymmetricSequence.pointwiseTensorBimapModuleLevelLaw sphereSequence.{u} f g
    (pointwiseTensorMap f g) q

/-- 両変数のスペクトル射は各段の通常のsmashの射になる。 -/
lemma pointwiseTensorMap_level {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {A B : SymmetricSpectrum.{u}} (g : A ⟶ B) (q : ℕ) :
    pointwiseTensorBimapLevelLaw f g q :=
  SymmetricSequence.pointwiseTensorBimapModuleLevelLaw_of_post sphereSequence.{u} f g
    (pointwiseTensorPost f A) q (pointwiseTensorPost_level f A q)

end SerrePositivity.SymmetricSpectrum
