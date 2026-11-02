module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHom
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorSymmetric

/-! # 対称スペクトルの閉対称モノイダル構造

球面上のテンソル積と内部Homの随伴を特殊化し、閉構造を登録する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 内部Homスペクトルの値域に関する関手。 -/
def internalHomFunctor (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.internalHomFunctor sphereSequence.{u} E

/-- 内部Hom関手の対象は構成済みの内部Homスペクトル。 -/
lemma internalHomFunctor_obj (E F : SymmetricSpectrum.{u}) :
    (internalHomFunctor E).obj F = internalHom E F := rfl

/-- 球面上のテンソル積からの射のスペクトルとしての転置。 -/
def internalHomCurry {E X F : SymmetricSpectrum.{u}} (f : sphereTensor E X ⟶ F) :
    X ⟶ internalHom E F := MonoidalModuleInternalHom.curryModule sphereSequence.{u} E f

/-- 内部Homへのスペクトル射の逆転置。 -/
def internalHomUncurry {E X F : SymmetricSpectrum.{u}} (f : X ⟶ internalHom E F) :
    sphereTensor E X ⟶ F := MonoidalModuleInternalHom.uncurryModule sphereSequence.{u} E f

/-- テンソル積からの射と内部Homへの射の全単射。 -/
def sphereTensorHomEquiv (E X F : SymmetricSpectrum.{u}) :
    (sphereTensor E X ⟶ F) ≃ (X ⟶ internalHom E F) :=
  MonoidalModuleInternalHom.tensorHomEquiv sphereSequence.{u} E X F

/-- 球面上のテンソル積と内部Homの随伴。 -/
def sphereTensorInternalHomAdjunction (E : SymmetricSpectrum.{u}) :
    tensorLeft E ⊣ internalHomFunctor E :=
  MonoidalModuleInternalHom.tensorInternalHomAdjunction sphereSequence.{u} E

/-- 対称スペクトル圏の閉モノイダル構造。 -/
instance spectrumMonoidalClosed : MonoidalClosed SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.moduleMonoidalClosed sphereSequence.{u}

/-- 登録した内部Homは構成済みの内部Homスペクトル。 -/
lemma ihom_eq_internalHom (E F : SymmetricSpectrum.{u}) :
    (ihom E).obj F = internalHom E F := rfl

/-- 登録した閉構造の評価は構成済みのスペクトル射としての評価。 -/
lemma ihom_ev_eq_internalHomEvaluation (E F : SymmetricSpectrum.{u}) :
    (ihom.ev E).app F = internalHomEvaluationSpectrum E F :=
  MonoidalModuleInternalHom.ihom_ev sphereSequence.{u} E F

/-- 登録したcurryingは構成済みの転置に一致する。 -/
lemma curry_eq_internalHomCurry {E X F : SymmetricSpectrum.{u}}
    (f : sphereTensor E X ⟶ F) : curry f = internalHomCurry f :=
  MonoidalModuleInternalHom.closed_curry sphereSequence.{u} E f

/-- 転置はパラメータ加群の射に関して自然。 -/
lemma internalHomCurry_naturality {E X Y F : SymmetricSpectrum.{u}}
    (g : X ⟶ Y) (f : sphereTensor E Y ⟶ F) :
    internalHomCurry (sphereTensorMap (𝟙 E) g ≫ f) = g ≫ internalHomCurry f :=
  MonoidalModuleInternalHom.curryModule_naturality sphereSequence.{u} E g f

/-- 転置は値域スペクトルの射に関して自然。 -/
lemma internalHomCurry_naturality_right {E X F G : SymmetricSpectrum.{u}}
    (f : sphereTensor E X ⟶ F) (g : F ⟶ G) :
    internalHomCurry (f ≫ g) = internalHomCurry f ≫ (internalHomFunctor E).map g :=
  MonoidalModuleInternalHom.curryModule_naturality_right sphereSequence.{u} E f g

/-- 転置と逆転置の合成は元のテンソル積からの射。 -/
@[simp]
lemma internalHomUncurry_curry {E X F : SymmetricSpectrum.{u}}
    (f : sphereTensor E X ⟶ F) : internalHomUncurry (internalHomCurry f) = f :=
  (sphereTensorHomEquiv E X F).left_inv f

/-- 逆転置と転置の合成は元の内部Homへの射。 -/
@[simp]
lemma internalHomCurry_uncurry {E X F : SymmetricSpectrum.{u}}
    (f : X ⟶ internalHom E F) : internalHomCurry (internalHomUncurry f) = f :=
  (sphereTensorHomEquiv E X F).right_inv f

/-- 転置と評価の合成は商からの元の射。 -/
@[reassoc (attr := simp)]
lemma internalHomCurry_evaluation {E X F : SymmetricSpectrum.{u}}
    (f : sphereTensor E X ⟶ F) :
    E.X ◁ (internalHomCurry f).hom ≫ internalHomEvaluation E F =
      tensorProjection E X ≫ f.hom :=
  MonoidalModuleInternalHom.curryUnderlying_evaluation sphereSequence.{u} E f

/-- 逆転置は商の標準射上で評価の合成に一致する。 -/
@[reassoc (attr := simp)]
lemma tensorProjection_internalHomUncurry {E X F : SymmetricSpectrum.{u}}
    (f : X ⟶ internalHom E F) :
    tensorProjection E X ≫ (internalHomUncurry f).hom =
      E.X ◁ f.hom ≫ internalHomEvaluation E F :=
  MonoidalModuleInternalHom.projection_uncurryModule sphereSequence.{u} E f

end SerrePositivity.SymmetricSpectrum
