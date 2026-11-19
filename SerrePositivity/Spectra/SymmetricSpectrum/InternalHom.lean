module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomUnderlying

/-! # 球面作用を持つ内部Homスペクトルと評価

内部Homの基礎対称列に球面作用を与え、球面上のテンソル積からの評価射を構成する。
テンソル積との随伴と閉構造の登録は後続の段階で行う。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面上の内部Homスペクトル。 -/
def internalHom (E F : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.moduleObj sphereSequence.{u} E F

/-- 内部Homスペクトルの基礎対称列は構成済みの等化子。 -/
lemma internalHom_underlying (E F : SymmetricSpectrum.{u}) :
    (internalHom E F).X = internalHomUnderlying E F := rfl

/-- 内部Homの球面作用を評価を介して記述する。 -/
@[reassoc]
lemma internalHom_action_evaluation (E F : SymmetricSpectrum.{u}) :
    E.X ◁ action (internalHom E F) ≫ internalHomEvaluation E F =
      (α_ E.X sphereSequence.{u} (internalHomUnderlying E F)).inv ≫
        ((β_ E.X sphereSequence.{u}).hom ≫ action E) ▷ internalHomUnderlying E F ≫
          internalHomEvaluation E F :=
  MonoidalModuleInternalHom.action_evaluation sphereSequence.{u} E F

/-- 球面上のテンソル積からのスペクトル射としての評価。 -/
def internalHomEvaluationSpectrum (E F : SymmetricSpectrum.{u}) :
    sphereTensor E (internalHom E F) ⟶ F :=
  MonoidalModuleInternalHom.evaluationModule sphereSequence.{u} E F

/-- スペクトルの評価は商の標準射上で基礎対称列の評価に一致する。 -/
@[reassoc (attr := simp)]
lemma tensorProjection_internalHomEvaluation (E F : SymmetricSpectrum.{u}) :
    tensorProjection E (internalHom E F) ≫
      (internalHomEvaluationSpectrum E F).hom = internalHomEvaluation E F :=
  MonoidalModuleInternalHom.projection_evaluationModule sphereSequence.{u} E F

end SerrePositivity.SymmetricSpectrum
