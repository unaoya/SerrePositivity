module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.SymmetricSpectrum.Free
public import SerrePositivity.Spectra.General.Limits
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # 対称スペクトルの内部Homの基礎対称列

球面作用と両立するパラメータ付き射を等化子で表す。
基礎対称列の構成であり、球面作用とスペクトル圏の閉構造は後続の段階で構成する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 球面作用に関する線形射を表す等化子の対称列。 -/
def internalHomUnderlying (E F : SymmetricSpectrum.{u}) : PointedSymmetricSequence.{u} :=
  MonoidalModuleInternalHom.obj sphereSequence.{u} E F

/-- 基礎対称列の通常の内部Homへの標準射。 -/
def internalHomInclusion (E F : SymmetricSpectrum.{u}) :
    internalHomUnderlying E F ⟶ (E.X ⟶[PointedSymmetricSequence.{u}] F.X) :=
  MonoidalModuleInternalHom.inclusion sphereSequence.{u} E F

instance internalHomInclusion_mono (E F : SymmetricSpectrum.{u}) :
    Mono (internalHomInclusion E F) :=
  MonoidalModuleInternalHom.inclusion_mono sphereSequence.{u} E F

/-- 等化子の基礎対称列上での評価射。 -/
def internalHomEvaluation (E F : SymmetricSpectrum.{u}) :
    E.X ⊗ internalHomUnderlying E F ⟶ F.X :=
  MonoidalModuleInternalHom.evaluation sphereSequence.{u} E F

/-- 評価は第一変数の球面作用と両立する。 -/
lemma internalHomEvaluation_linear (E F : SymmetricSpectrum.{u}) :
    action E ▷ internalHomUnderlying E F ≫ internalHomEvaluation E F =
      (α_ sphereSequence.{u} E.X (internalHomUnderlying E F)).hom ≫
        sphereSequence.{u} ◁ internalHomEvaluation E F ≫ action F :=
  MonoidalModuleInternalHom.evaluation_linear sphereSequence.{u} E F

/-- 内部Homの基礎対称列への射と、右convolutionからのスペクトル射の全単射。 -/
def internalHomUnderlyingEquiv (E F : SymmetricSpectrum.{u})
    (X : PointedSymmetricSequence.{u}) : (X ⟶ internalHomUnderlying E F) ≃
      (MonoidalBalancedTensor.tensorRightObj sphereSequence.{u} E X ⟶ F) :=
  MonoidalModuleInternalHom.moduleHomEquiv sphereSequence.{u} E F X

/-- Hom同値はパラメータとなる対称列の射に関して自然。 -/
lemma internalHomUnderlyingEquiv_naturality (E F : SymmetricSpectrum.{u})
    {X Y : PointedSymmetricSequence.{u}} (g : X ⟶ Y)
    (f : Y ⟶ internalHomUnderlying E F) :
    internalHomUnderlyingEquiv E F X (g ≫ f) =
      MonoidalBalancedTensor.tensorRightMap sphereSequence.{u} (𝟙 E) g ≫
        internalHomUnderlyingEquiv E F Y f :=
  MonoidalModuleInternalHom.moduleUnlift_naturality sphereSequence.{u} E F g f

end SerrePositivity.SymmetricSpectrum
