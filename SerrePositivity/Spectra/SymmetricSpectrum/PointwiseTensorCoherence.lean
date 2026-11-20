module

import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAssociatorLevels
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorUnit
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorMapLevels

/-! # 各段のsmashによる作用の単位と結合の整合性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 生成対象の射の各段の公式を等式として使う。 -/
lemma pointwiseTensorPost_app {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorPost f E).hom.app (FiniteBijection.of q) = f ▷ level E q :=
  pointwiseTensorPost_level f E q

/-- 単位比較の各段の公式を等式として使う。 -/
lemma pointwiseTensorUnitIso_app (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorUnitIso E).hom.hom.app (FiniteBijection.of q) =
      (λ_ (level E q)).hom := by
  have h : pointwiseTensorUnitIso E = GeneralSymmetricSpectrum.pointwiseTensorUnitIso E := rfl
  rw [h]
  exact GeneralSymmetricSpectrum.pointwiseTensorUnitIso_level E q

/-- 作用の五角形の等式。 -/
def pointwiseTensorPentagonLaw (X Y Z : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) : Prop :=
  SymmetricSequence.pointwiseActionPentagonLaw sphereSequence.{u}
    pointwiseTensorAssociator.{u} pointwiseTensorPost.{u} X Y Z E

/-- 作用の結同比較は五角形の等式を満たす。 -/
lemma pointwiseTensor_pentagon (X Y Z : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) : pointwiseTensorPentagonLaw X Y Z E :=
  SymmetricSequence.pointwiseAction_pentagon sphereSequence.{u}
    pointwiseTensorAssociator.{u} pointwiseTensorPost.{u}
    pointwiseTensorAssociator_level.{u} pointwiseTensorPost_app.{u} X Y Z E

/-- 作用の右単位の三角形の等式。 -/
def pointwiseTensorTriangleLaw (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) : Prop :=
  SymmetricSequence.pointwiseActionTriangleLaw sphereSequence.{u}
    pointwiseTensorAssociator.{u} pointwiseTensorUnitIso.{u} pointwiseTensorPost.{u} X E

/-- 作用の結同比較は通常のsmashの右単位と整合する。 -/
lemma pointwiseTensor_triangle (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorTriangleLaw X E :=
  SymmetricSequence.pointwiseAction_triangle sphereSequence.{u}
    pointwiseTensorAssociator.{u} pointwiseTensorUnitIso.{u} pointwiseTensorPost.{u}
    pointwiseTensorAssociator_level.{u} pointwiseTensorUnitIso_app.{u}
    pointwiseTensorPost_app.{u} X E

/-- 作用の左単位の整合性の等式。 -/
def pointwiseTensorLeftUnitLaw (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) : Prop :=
  SymmetricSequence.pointwiseActionLeftUnitLaw sphereSequence.{u}
    pointwiseTensorAssociator.{u} pointwiseTensorUnitIso.{u} pointwiseTensorPost.{u} X E

/-- 作用の結同比較は通常のsmashの左単位と整合する。 -/
lemma pointwiseTensor_left_unit (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorLeftUnitLaw X E :=
  SymmetricSequence.pointwiseAction_left_unit sphereSequence.{u}
    pointwiseTensorAssociator.{u} pointwiseTensorUnitIso.{u} pointwiseTensorPost.{u}
    pointwiseTensorAssociator_level.{u} pointwiseTensorUnitIso_app.{u}
    pointwiseTensorPost_app.{u} X E

end SerrePositivity.SymmetricSpectrum
