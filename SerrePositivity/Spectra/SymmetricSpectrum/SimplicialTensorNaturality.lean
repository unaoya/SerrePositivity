module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorCotensor
public import SerrePositivity.Spectra.General.ParametrizedMapping
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # 通常の単体的集合による三つのHom同値の自然性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensorPost)

open CategoryTheory
open SerrePositivity.PointedSimplicialSet

/-- 単体的集合の射をtensorの生成対象へ送る。 -/
def simplicialTensorPost {K L : SSet.{u}} (f : K ⟶ L) (E : SymmetricSpectrum.{u}) :
    simplicialTensor K E ⟶ simplicialTensor L E :=
  pointwiseTensorPost (adjoinBasepointFunctor.map f) E

/-- 単体的集合の射によるcotensorの前合成。 -/
def simplicialCotensorPre {K L : SSet.{u}} (f : K ⟶ L) (F : SymmetricSpectrum.{u}) :
    simplicialCotensor L F ⟶ simplicialCotensor K F :=
  ((GeneralSymmetricSpectrum.cotensorBifunctor (K := circle.{u})).map
    (adjoinBasepointFunctor.map f).op).app F

/-- 原変数スペクトルの射による通常の単体的写像対象の前合成。 -/
def simplicialMappingSpacePre {E E' : SymmetricSpectrum.{u}} (f : E' ⟶ E)
    (F : SymmetricSpectrum.{u}) : simplicialMappingSpace E F ⟶ simplicialMappingSpace E' F :=
  PointedSimplicialSet.forget.map ((pointedMappingSpaceBifunctor.map f.op).app F)

/-- cotensorへのHom同値の単体的集合に関する自然性。 -/
lemma simplicialTensorCotensorHomEquiv_post {K L : SSet.{u}} (f : K ⟶ L)
    {E F : SymmetricSpectrum.{u}} (g : simplicialTensor L E ⟶ F) :
    ((simplicialTensorCotensorAdjunction K).homEquiv E F) (simplicialTensorPost f E ≫ g) =
      ((simplicialTensorCotensorAdjunction L).homEquiv E F) g ≫ simplicialCotensorPre f F :=
  GeneralSymmetricSpectrum.pointwiseTensorHomEquiv_naturality_parameter
    (adjoinBasepointFunctor.map f) E F g

end SerrePositivity.SymmetricSpectrum
