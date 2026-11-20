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
    SSet.{u} ⥤ SymmetricSpectrum.{u} := adjoinBasepointFunctor ⋙ mappingTensorFunctor E

/-- 基点を忘れた写像対象の値域スペクトルに関する関手。 -/
def simplicialMappingSpaceFunctor (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} ⥤ SSet.{u} := pointedMappingSpaceFunctor E ⋙ PointedSimplicialSet.forget

/-- tensorの単体的集合パラメータと通常の単体的写像対象の随伴。 -/
def simplicialTensorMappingAdjunction (E : SymmetricSpectrum.{u}) :
    simplicialTensorParameterFunctor E ⊣ simplicialMappingSpaceFunctor E :=
  adjoinBasepointAdjunction.comp (pointedMappingSpaceAdjunction E)

/-- 単体的集合によるtensorとcotensorの随伴。 -/
def simplicialTensorCotensorAdjunction (K : SSet.{u}) :
    simplicialTensorFunctor K ⊣ simplicialCotensorFunctor K :=
  pointwiseTensorCotensorAdjunction (adjoinBasepoint K)

/-- tensorからの射と通常の単体的写像対象への射のHom同値。 -/
def simplicialTensorMappingHomEquiv (K : SSet.{u}) (E F : SymmetricSpectrum.{u}) :
    (simplicialTensor K E ⟶ F) ≃ (K ⟶ simplicialMappingSpace E F) :=
  (simplicialTensorMappingAdjunction E).homEquiv K F

/-- 通常の写像対象への射とcotensorへの射のHom同値。 -/
def simplicialMappingCotensorHomEquiv (K : SSet.{u}) (E F : SymmetricSpectrum.{u}) :
    (K ⟶ simplicialMappingSpace E F) ≃ (E ⟶ simplicialCotensor K F) :=
  (simplicialTensorMappingHomEquiv K E F).symm.trans
    ((simplicialTensorCotensorAdjunction K).homEquiv E F)

/-- 通常の単体的写像対象の評価。 -/
def simplicialMappingEvaluation (E F : SymmetricSpectrum.{u}) :
    simplicialTensor (simplicialMappingSpace E F) E ⟶ F :=
  (simplicialTensorMappingAdjunction E).counit.app F

/-- 単体的集合から通常の写像対象への余評価。 -/
def simplicialMappingCoevaluation (K : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    K ⟶ simplicialMappingSpace E (simplicialTensor K E) :=
  (simplicialTensorMappingAdjunction E).unit.app K

/-- 写像対象へのHom同値は単体的集合の射に関して自然。 -/
lemma simplicialTensorMappingHomEquiv_naturality_left {K L : SSet.{u}} (f : K ⟶ L)
    {E F : SymmetricSpectrum.{u}} (g : simplicialTensor L E ⟶ F) :
    AdjunctionHomLaws.curryNaturalityLeftLaw (simplicialTensorMappingAdjunction E) f g :=
  AdjunctionHomLaws.curry_naturality_left (simplicialTensorMappingAdjunction E) f g

/-- 写像対象へのHom同値は値域スペクトルの射に関して自然。 -/
lemma simplicialTensorMappingHomEquiv_naturality_right (K : SSet.{u})
    {E F G : SymmetricSpectrum.{u}} (f : simplicialTensor K E ⟶ F) (g : F ⟶ G) :
    AdjunctionHomLaws.curryNaturalityRightLaw (simplicialTensorMappingAdjunction E) f g :=
  AdjunctionHomLaws.curry_naturality_right (simplicialTensorMappingAdjunction E) f g

/-- 三つのHom同値の順写像は同じ転置に一致する。 -/
lemma simplicialHomEquiv_compatibility (K : SSet.{u}) (E F : SymmetricSpectrum.{u})
    (f : simplicialTensor K E ⟶ F) :
    simplicialMappingCotensorHomEquiv K E F (simplicialTensorMappingHomEquiv K E F f) =
      ((simplicialTensorCotensorAdjunction K).homEquiv E F) f := by
  unfold simplicialMappingCotensorHomEquiv
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

end SerrePositivity.SymmetricSpectrum
