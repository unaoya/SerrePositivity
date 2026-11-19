module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorAdjunction

/-! # 各段のsmashを持つテンソルとcotensorの随伴 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段の通常のsmashを持つテンソルはcotensor関手の左随伴。 -/
def pointwiseTensorCotensorAdjunction (X : PointedSimplicialSet.{u}) :
    pointwiseTensorFunctor X ⊣ cotensorFunctor X :=
  (freeZeroTensorCotensorAdjunction X).ofNatIsoLeft (sphereTensorFreeZeroPointwiseNatIso X)

/-- 転置はパラメータスペクトルの射に関して自然。 -/
lemma pointwiseTensorCurry_naturality (X : PointedSimplicialSet.{u})
    {A B E : SymmetricSpectrum.{u}} (g : A ⟶ B) (f : pointwiseTensor X B ⟶ E) :
    ((pointwiseTensorCotensorAdjunction X).homEquiv _ _) ((pointwiseTensorFunctor X).map g ≫ f) =
      g ≫ ((pointwiseTensorCotensorAdjunction X).homEquiv _ _) f :=
  (pointwiseTensorCotensorAdjunction X).homEquiv_naturality_left g f

/-- 転置は値域スペクトルの射に関して自然。 -/
lemma pointwiseTensorCurry_naturality_right (X : PointedSimplicialSet.{u})
    {A E F : SymmetricSpectrum.{u}} (f : pointwiseTensor X A ⟶ E) (g : E ⟶ F) :
    ((pointwiseTensorCotensorAdjunction X).homEquiv _ _) (f ≫ g) =
      ((pointwiseTensorCotensorAdjunction X).homEquiv _ _) f ≫ (cotensorFunctor X).map g :=
  (pointwiseTensorCotensorAdjunction X).homEquiv_naturality_right f g

end SerrePositivity.SymmetricSpectrum
