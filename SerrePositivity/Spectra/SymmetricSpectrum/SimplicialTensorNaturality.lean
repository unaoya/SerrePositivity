module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorCotensor
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceNaturality
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
  cotensorPre (adjoinBasepointFunctor.map f) F

/-- 原変数スペクトルの射による通常の単体的写像対象の前合成。 -/
def simplicialMappingSpacePre {E E' : SymmetricSpectrum.{u}} (f : E' ⟶ E)
    (F : SymmetricSpectrum.{u}) : simplicialMappingSpace E F ⟶ simplicialMappingSpace E' F :=
  PointedSimplicialSet.forget.map (pointedMappingSpacePre f F)

/-- 写像対象へのHom同値の原変数スペクトルの自然性。 -/
def simplicialTensorMappingPreLaw (K : SSet.{u}) {E E' F : SymmetricSpectrum.{u}}
    (f : E' ⟶ E) (g : simplicialTensor K E ⟶ F) : Prop :=
  MonoidalMappingAdjunction.compositeTransportedPreLaw (freeAtAdjunction 0)
    adjoinBasepointAdjunction.{u} f (mappingTensorNatIso E) (mappingTensorNatIso E')
    ((simplicialTensorFunctor K).map f) g

/-- 基点追加の随伴を通して原変数スペクトルの自然性を得る。 -/
lemma simplicialTensorMappingHomEquiv_pre (K : SSet.{u})
    {E E' F : SymmetricSpectrum.{u}} (f : E' ⟶ E) (g : simplicialTensor K E ⟶ F) :
    simplicialTensorMappingPreLaw K f g :=
  MonoidalMappingAdjunction.composite_transported_pre (freeAtAdjunction 0)
    adjoinBasepointAdjunction.{u} f (mappingTensorNatIso E) (mappingTensorNatIso E')
    ((simplicialTensorFunctor K).map f) g
    ((sphereTensorFreeZeroPointwiseNatIso (adjoinBasepoint K)).hom.naturality f)

/-- cotensorへのHom同値の単体的集合に関する自然性。 -/
lemma simplicialTensorCotensorHomEquiv_post {K L : SSet.{u}} (f : K ⟶ L)
    {E F : SymmetricSpectrum.{u}} (g : simplicialTensor L E ⟶ F) :
    simplicialTensorCotensorHomEquiv K E F (simplicialTensorPost f E ≫ g) =
      simplicialTensorCotensorHomEquiv L E F g ≫ simplicialCotensorPre f F :=
  pointwiseTensorCurry_post (adjoinBasepointFunctor.map f) g

/-- 写像対象とcotensorのHom同値の単体的集合に関する自然性の法則。 -/
def simplicialMappingCotensorParameterLaw {K L : SSet.{u}} (f : K ⟶ L)
    (E F : SymmetricSpectrum.{u}) (g : L ⟶ simplicialMappingSpace E F) : Prop :=
  HomEquivNaturality.derivedLaw (simplicialTensorMappingHomEquiv L E F)
    (simplicialTensorMappingHomEquiv K E F) (simplicialTensorCotensorHomEquiv L E F)
    (simplicialTensorCotensorHomEquiv K E F) (fun h => f ≫ h)
    (fun h => h ≫ simplicialCotensorPre f F) g

/-- 二つのHom同値の自然性から第三のHom同値の単体的集合の自然性を得る。 -/
lemma simplicialMappingCotensorHomEquiv_parameter {K L : SSet.{u}} (f : K ⟶ L)
    (E F : SymmetricSpectrum.{u}) (g : L ⟶ simplicialMappingSpace E F) :
    simplicialMappingCotensorParameterLaw f E F g :=
  HomEquivNaturality.derived (simplicialTensorMappingHomEquiv L E F)
    (simplicialTensorMappingHomEquiv K E F) (simplicialTensorCotensorHomEquiv L E F)
    (simplicialTensorCotensorHomEquiv K E F) (fun h => simplicialTensorPost f E ≫ h)
    (fun h => f ≫ h) (fun h => h ≫ simplicialCotensorPre f F)
    (fun h => simplicialTensorMappingHomEquiv_naturality_left f h)
    (fun h => simplicialTensorCotensorHomEquiv_post f h) g

/-- 写像対象とcotensorのHom同値の原変数スペクトルに関する自然性の法則。 -/
def simplicialMappingCotensorSourceLaw (K : SSet.{u}) {E E' F : SymmetricSpectrum.{u}}
    (f : E' ⟶ E) (g : K ⟶ simplicialMappingSpace E F) : Prop :=
  MonoidalMappingAdjunction.compositeDerivedPreLaw (freeAtAdjunction 0)
    adjoinBasepointAdjunction.{u} f (mappingTensorNatIso E) (mappingTensorNatIso E')
    (simplicialTensorCotensorHomEquiv K E F) (simplicialTensorCotensorHomEquiv K E' F)
    (fun h => f ≫ h) g

/-- 二つのHom同値の自然性から第三のHom同値の原変数の自然性を得る。 -/
lemma simplicialMappingCotensorHomEquiv_source (K : SSet.{u})
    {E E' F : SymmetricSpectrum.{u}} (f : E' ⟶ E) (g : K ⟶ simplicialMappingSpace E F) :
    simplicialMappingCotensorSourceLaw K f g :=
  MonoidalMappingAdjunction.composite_derived_pre (freeAtAdjunction 0)
    adjoinBasepointAdjunction.{u} f (mappingTensorNatIso E) (mappingTensorNatIso E')
    (simplicialTensorCotensorHomEquiv K E F) (simplicialTensorCotensorHomEquiv K E' F)
    ((simplicialTensorFunctor K).map f) (fun h => f ≫ h)
    ((sphereTensorFreeZeroPointwiseNatIso (adjoinBasepoint K)).hom.naturality f)
    (fun h => simplicialTensorCotensorHomEquiv_naturality_left K f h) g

/-- 写像対象とcotensorのHom同値の値域スペクトルに関する自然性の法則。 -/
def simplicialMappingCotensorTargetLaw (K : SSet.{u}) {E F G : SymmetricSpectrum.{u}}
    (f : F ⟶ G) (g : K ⟶ simplicialMappingSpace E F) : Prop :=
  HomEquivNaturality.derivedLaw (simplicialTensorMappingHomEquiv K E F)
    (simplicialTensorMappingHomEquiv K E G) (simplicialTensorCotensorHomEquiv K E F)
    (simplicialTensorCotensorHomEquiv K E G)
    (fun h => h ≫ (simplicialMappingSpaceFunctor E).map f)
    (fun h => h ≫ (simplicialCotensorFunctor K).map f) g

/-- 二つのHom同値の自然性から第三のHom同値の値域の自然性を得る。 -/
lemma simplicialMappingCotensorHomEquiv_target (K : SSet.{u})
    {E F G : SymmetricSpectrum.{u}} (f : F ⟶ G) (g : K ⟶ simplicialMappingSpace E F) :
    simplicialMappingCotensorTargetLaw K f g :=
  HomEquivNaturality.derived (simplicialTensorMappingHomEquiv K E F)
    (simplicialTensorMappingHomEquiv K E G) (simplicialTensorCotensorHomEquiv K E F)
    (simplicialTensorCotensorHomEquiv K E G) (fun h => h ≫ f)
    (fun h => h ≫ (simplicialMappingSpaceFunctor E).map f)
    (fun h => h ≫ (simplicialCotensorFunctor K).map f)
    (fun h => simplicialTensorMappingHomEquiv_naturality_right K h f)
    (fun h => simplicialTensorCotensorHomEquiv_naturality_right K h f) g

end SerrePositivity.SymmetricSpectrum
