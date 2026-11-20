module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleMap
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLeftUncurry

/-! # cotensorの射と各段の通常の内部Homの射 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet
open MonoidalModuleInternalHom (freeHomModuleIso)

/-- cotensorの二変数の射は、内部Homの射を全体の比較の順逆で移した射。 -/
lemma cotensorMap_conjugate {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    (internalHomCotensorIso Y E).inv ≫ MonoidalModuleInternalHom.homMap sphereSequence.{u} ((freeAt 0).map f) g ≫
        (internalHomCotensorIso X F).hom = cotensorMap f g := by
  change (internalHomCotensorIso Y E).inv ≫
      (MonoidalModuleInternalHom.preMap sphereSequence.{u} ((freeAt 0).map f) E ≫ (GeneralSymmetricSpectrum.internalHomFunctor ((freeAt 0).obj X)).map g) ≫
        (internalHomCotensorIso X F).hom = _
  simp only [Category.assoc]
  exact FunctorTransport.bimap_conjugate internalHomCotensorBifunctorIso f.op g

/-- 全体の比較の順射は、自由原変数の比較と基礎対称列の比較の合成。 -/
lemma internalHomCotensorIso_hom_hom (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomCotensorIso X E).hom.hom =
      (freeHomModuleIso sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E).hom.hom ≫ (homBySequenceCotensorIso X E).hom := rfl

/-- cotensorの基礎射が通常の内部Homの前合成・後合成になるという法則。 -/
def cotensorMapLaw {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) : Prop :=
  SymmetricSequence.unshiftedInternalHomMapLaw f g.hom
    ((Iso.refl (cotensor Y E).X).inv ≫ (cotensorMap f g).hom ≫
      (Iso.refl (cotensor X F).X).hom)

/-- cotensorのスペクトル射は、通常の前合成・後合成の法則を満たす。 -/
lemma cotensorMap_law {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) : cotensorMapLaw f g := by
  unfold cotensorMapLaw
  apply SymmetricSequence.freeZeroModuleMap_law sphereSequence.{u} f g
    (internalHomCotensorIso Y E) (internalHomCotensorIso X F) (cotensorMap f g)
    (homBySequenceCotensorIso Y E) (homBySequenceCotensorIso X F)
    (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
    exact internalHomCotensorIso_inv_hom Y E
  · simp only [Iso.refl_inv]
    exact internalHomCotensorIso_hom_hom X F
  · exact cotensorMap_conjugate f g
  · rfl
  · rfl

/-- cotensorの第q段の射を、通常の内部Homの前合成・後合成で記述する。 -/
def cotensorLevelMap (q : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    (ihom Y).obj (level E q) ⟶ (ihom X).obj (level F q) :=
  (pre f).app (level E q) ≫ (ihom X).map (g.hom.app (FiniteBijection.of q))

/-- cotensorの射の第q段が通常の内部Homの前合成・後合成になるという法則。 -/
def cotensorMapLevelLaw (q : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) : Prop :=
  SymmetricSequence.unshiftedInternalHomMapLevelLaw f g.hom
    ((Iso.refl (cotensor Y E).X).inv ≫ (cotensorMap f g).hom ≫
      (Iso.refl (cotensor X F).X).hom) q

/-- cotensorのスペクトル射は、各段で通常の前合成・後合成の公式を満たす。 -/
lemma cotensorMap_app (q : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) : cotensorMapLevelLaw q f g :=
  SymmetricSequence.unshiftedInternalHomMapLaw_levelLaw f g.hom
    ((Iso.refl (cotensor Y E).X).inv ≫ (cotensorMap f g).hom ≫
      (Iso.refl (cotensor X F).X).hom) q (cotensorMap_law f g)

end SerrePositivity.SymmetricSpectrum
