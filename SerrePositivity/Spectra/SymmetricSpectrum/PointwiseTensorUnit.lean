module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroUnit
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleUnit
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModuleUnit
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeMonoidal

/-! # 各段のsmashによる作用の単位比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- S^0から第0段を自由生成するスペクトルと球面スペクトルの比較。 -/
def freeZeroUnitIso : (freeAt 0).obj (𝟙_ PointedSimplicialSet.{u}) ≅ sphere.{u} :=
  SymmetricSequence.freeZeroModuleUnitIso sphereSequence.{u}

/-- F_0 S^0の生成元を単位比較で球面の単位へ送るという法則。 -/
def freeZeroUnitGeneratorLaw : Prop :=
  SymmetricSequence.freeZeroModuleUnitGeneratorLaw sphereSequence.{u}
    (freeAtGenerator 0 (𝟙_ PointedSimplicialSet.{u}))

/-- 球面スペクトルへの単位比較は第0段の生成元を球面の単位へ送る。 -/
lemma freeZeroUnitIso_generator : freeZeroUnitGeneratorLaw.{u} :=
  SymmetricSequence.freeZeroModuleUnitGenerator_law sphereSequence.{u}
    (freeAtGenerator 0 (𝟙_ PointedSimplicialSet.{u}))
    (GeneralSymmetricSpectrum.freeAtGenerator_eq (K := circle.{u}) 0 (𝟙_ PointedSimplicialSet.{u}))

/-- 単位比較を値域スペクトルに関する自然同型へまとめる。 -/
def pointwiseTensorUnitNatIso :
    pointwiseTensorFunctor (𝟙_ PointedSimplicialSet.{u}) ≅ 𝟭 SymmetricSpectrum.{u} :=
  SymmetricSequence.pointwiseTensorModuleUnitNatIso sphereSequence.{u}

/-- 各段のsmashを持つテンソルの作用の単位比較。 -/
def pointwiseTensorUnitIso (E : SymmetricSpectrum.{u}) :
    pointwiseTensor (𝟙_ PointedSimplicialSet.{u}) E ≅ E := pointwiseTensorUnitNatIso.app E

/-- 単位比較は値域スペクトルの射に関して自然。 -/
@[reassoc]
lemma pointwiseTensorUnitIso_naturality {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    (pointwiseTensorFunctor (𝟙_ PointedSimplicialSet.{u})).map f ≫
        (pointwiseTensorUnitIso F).hom = (pointwiseTensorUnitIso E).hom ≫ f :=
  pointwiseTensorUnitNatIso.hom.naturality f

/-- スペクトルの単位比較の各段が通常のsmashの左単位子になるという法則。 -/
def pointwiseTensorUnitLevelLaw (E : SymmetricSpectrum.{u}) (q : ℕ) : Prop :=
  SymmetricSequence.pointwiseTensorModuleUnitLevelLaw sphereSequence.{u} E q

/-- 作用の単位比較は各段の通常のsmashの左単位子に一致する。 -/
lemma pointwiseTensorUnitIso_level (E : SymmetricSpectrum.{u}) (q : ℕ) :
    pointwiseTensorUnitLevelLaw E q :=
  SymmetricSequence.pointwiseTensorModuleUnit_levelLaw sphereSequence.{u} E q

end SerrePositivity.SymmetricSpectrum
