module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpace

/-! # 基点付き写像対象への転置の原変数に関する自然性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor)

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 原変数スペクトルの射による基点付き写像対象の前合成。 -/
def pointedMappingSpacePre {E E' : SymmetricSpectrum.{u}} (f : E' ⟶ E)
    (F : SymmetricSpectrum.{u}) : pointedMappingSpace E F ⟶ pointedMappingSpace E' F :=
  (pointedMappingSpaceBifunctor.map f.op).app F

/-- 二変数関手の原変数の射は、選択済みの前合成。 -/
lemma pointedMappingSpaceBifunctor_map {E E' : SymmetricSpectrum.{u}} (f : E' ⟶ E)
    (F : SymmetricSpectrum.{u}) :
    (pointedMappingSpaceBifunctor.map f.op).app F = pointedMappingSpacePre f F := rfl

/-- 写像対象への転置の原変数スペクトルに関する自然性の法則。 -/
def mappingSpaceCurryPreLaw (X : PointedSimplicialSet.{u})
    {E E' F : SymmetricSpectrum.{u}} (f : E' ⟶ E) (g : pointwiseTensor X E ⟶ F) : Prop :=
  MonoidalMappingAdjunction.transportedPreLaw (freeAtAdjunction 0) f
    (mappingTensorNatIso E) (mappingTensorNatIso E') ((pointwiseTensorFunctor X).map f) g

/-- テンソルした原変数の射で前合成して転置すると、写像対象の前合成になる。 -/
lemma mappingSpaceCurry_pre (X : PointedSimplicialSet.{u})
    {E E' F : SymmetricSpectrum.{u}} (f : E' ⟶ E) (g : pointwiseTensor X E ⟶ F) :
    mappingSpaceCurryPreLaw X f g :=
  MonoidalMappingAdjunction.transported_pre (freeAtAdjunction 0) f
    (mappingTensorNatIso E) (mappingTensorNatIso E') ((pointwiseTensorFunctor X).map f) g
    ((sphereTensorFreeZeroPointwiseNatIso X).hom.naturality f)

/-- 写像対象からの逆転置の原変数スペクトルに関する自然性の法則。 -/
def mappingSpaceUncurryPreLaw (X : PointedSimplicialSet.{u})
    {E E' F : SymmetricSpectrum.{u}} (f : E' ⟶ E) (g : X ⟶ pointedMappingSpace E F) : Prop :=
  MonoidalMappingAdjunction.transportedUncurryPreLaw (freeAtAdjunction 0) f
    (mappingTensorNatIso E) (mappingTensorNatIso E') ((pointwiseTensorFunctor X).map f) g

/-- 写像対象の前合成の逆転置は、テンソルした原変数の射による前合成になる。 -/
lemma mappingSpaceUncurry_pre (X : PointedSimplicialSet.{u})
    {E E' F : SymmetricSpectrum.{u}} (f : E' ⟶ E) (g : X ⟶ pointedMappingSpace E F) :
    mappingSpaceUncurryPreLaw X f g :=
  MonoidalMappingAdjunction.transported_uncurry_pre (freeAtAdjunction 0) f
    (mappingTensorNatIso E) (mappingTensorNatIso E') ((pointwiseTensorFunctor X).map f) g
    ((sphereTensorFreeZeroPointwiseNatIso X).hom.naturality f)

end SerrePositivity.SymmetricSpectrum
