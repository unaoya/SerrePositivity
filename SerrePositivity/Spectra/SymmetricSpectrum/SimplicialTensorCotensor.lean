module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepoint
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceSimplicialOrdinary
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAdjunction

/-! # 通常の単体的集合によるtensor・cotensorと三つのHom同値 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor cotensor)

open CategoryTheory
open SerrePositivity.PointedSimplicialSet

/-- 通常の単体的集合によるtensorは、自由な基点を追加した各段のsmash。 -/
def simplicialTensor (K : SSet.{u}) (E : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} :=
  pointwiseTensor (adjoinBasepoint K) E

/-- 通常の単体的集合によるcotensorは、自由な基点を追加した対象からのcotensor。 -/
def simplicialCotensor (K : SSet.{u}) (E : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} :=
  cotensor (adjoinBasepoint K) E

/-- 固定した単体的集合によるtensor関手。 -/
def simplicialTensorFunctor (K : SSet.{u}) : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  pointwiseTensorFunctor (adjoinBasepoint K)

/-- 固定した単体的集合によるcotensor関手。 -/
def simplicialCotensorFunctor (K : SSet.{u}) : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  cotensorFunctor (adjoinBasepoint K)

/-- スペクトルを固定し、単体的集合を動かすtensor関手。 -/
def simplicialTensorParameterFunctor (E : SymmetricSpectrum.{u}) :
    SSet.{u} ⥤ SymmetricSpectrum.{u} :=
  adjoinBasepointFunctor ⋙ GeneralSymmetricSpectrum.mappingTensorFunctor E

/-- 基点を忘れた写像対象の値域スペクトルに関する関手。 -/
def simplicialMappingSpaceFunctor (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} ⥤ SSet.{u} :=
  GeneralSymmetricSpectrum.mappingObjectFunctor E ⋙ PointedSimplicialSet.forget

/-- tensorの単体的集合パラメータと通常の単体的写像対象の随伴。 -/
def simplicialTensorMappingAdjunction (E : SymmetricSpectrum.{u}) :
    simplicialTensorParameterFunctor E ⊣ simplicialMappingSpaceFunctor E :=
  adjoinBasepointAdjunction.comp (GeneralSymmetricSpectrum.mappingObjectAdjunction E)

/-- 単体的集合によるtensorとcotensorの随伴。 -/
def simplicialTensorCotensorAdjunction (K : SSet.{u}) :
    simplicialTensorFunctor K ⊣ simplicialCotensorFunctor K :=
  pointwiseTensorCotensorAdjunction (adjoinBasepoint K)

end SerrePositivity.SymmetricSpectrum
