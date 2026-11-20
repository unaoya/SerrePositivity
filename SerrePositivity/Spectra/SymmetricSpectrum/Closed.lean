module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHom
public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere

/-! # 対称スペクトルの閉対称モノイダル構造

球面上のテンソル積と内部Homの随伴を特殊化する。
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
def internalHomCurry {E X F : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor E X ⟶ F) :
    X ⟶ internalHom E F := MonoidalModuleInternalHom.curryModule sphereSequence.{u} E f

/-- 内部Homへのスペクトル射の逆転置。 -/
def internalHomUncurry {E X F : SymmetricSpectrum.{u}} (f : X ⟶ internalHom E F) :
    GeneralSymmetricSpectrum.tensor E X ⟶ F :=
  MonoidalModuleInternalHom.uncurryModule sphereSequence.{u} E f

/-- 球面上のテンソル積と内部Homの随伴。 -/
def sphereTensorInternalHomAdjunction (E : SymmetricSpectrum.{u}) :
    tensorLeft E ⊣ internalHomFunctor E :=
  MonoidalModuleInternalHom.tensorInternalHomAdjunction sphereSequence.{u} E

/-- 登録した内部Homは構成済みの内部Homスペクトル。 -/
lemma ihom_eq_internalHom (E F : SymmetricSpectrum.{u}) :
    (ihom E).obj F = internalHom E F := rfl

/-- 登録した閉構造の評価は構成済みのスペクトル射としての評価。 -/
lemma ihom_ev_eq_internalHomEvaluation (E F : SymmetricSpectrum.{u}) :
    (ihom.ev E).app F = internalHomEvaluationSpectrum E F :=
  MonoidalModuleInternalHom.ihom_ev sphereSequence.{u} E F

/-- 登録したcurryingは構成済みの転置に一致する。 -/
lemma curry_eq_internalHomCurry {E X F : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor E X ⟶ F) : curry f = internalHomCurry f :=
  MonoidalModuleInternalHom.closed_curry sphereSequence.{u} E f

/-- 転置はパラメータ加群の射に関して自然。 -/
lemma internalHomCurry_naturality {E X Y F : SymmetricSpectrum.{u}}
    (g : X ⟶ Y) (f : GeneralSymmetricSpectrum.tensor E Y ⟶ F) :
    internalHomCurry (MonoidalBalancedTensor.moduleMap sphereSequence.{u} (𝟙 E) g ≫ f) =
      g ≫ internalHomCurry f :=
  MonoidalModuleInternalHom.curryModule_naturality sphereSequence.{u} E g f

/-- 転置は値域スペクトルの射に関して自然。 -/
lemma internalHomCurry_naturality_right {E X F G : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor E X ⟶ F) (g : F ⟶ G) :
    internalHomCurry (f ≫ g) = internalHomCurry f ≫ (internalHomFunctor E).map g :=
  MonoidalModuleInternalHom.curryModule_naturality_right sphereSequence.{u} E f g

/-- 転置と逆転置の合成は元のテンソル積からの射。 -/
@[simp]
lemma internalHomUncurry_curry {E X F : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor E X ⟶ F) : internalHomUncurry (internalHomCurry f) = f :=
  (MonoidalModuleInternalHom.tensorHomEquiv sphereSequence.{u} E X F).left_inv f

/-- 逆転置と転置の合成は元の内部Homへの射。 -/
@[simp]
lemma internalHomCurry_uncurry {E X F : SymmetricSpectrum.{u}}
    (f : X ⟶ internalHom E F) : internalHomCurry (internalHomUncurry f) = f :=
  (MonoidalModuleInternalHom.tensorHomEquiv sphereSequence.{u} E X F).right_inv f

/-- 転置と評価の合成は商からの元の射。 -/
@[reassoc (attr := simp)]
lemma internalHomCurry_evaluation {E X F : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor E X ⟶ F) :
    E.X ◁ (internalHomCurry f).hom ≫ internalHomEvaluation E F =
      MonoidalBalancedTensor.projection sphereSequence.{u} E X ≫ f.hom :=
  MonoidalModuleInternalHom.curryUnderlying_evaluation sphereSequence.{u} E f

/-- 逆転置は商の標準射上で評価の合成に一致する。 -/
@[reassoc (attr := simp)]
lemma tensorProjection_internalHomUncurry {E X F : SymmetricSpectrum.{u}}
    (f : X ⟶ internalHom E F) :
    MonoidalBalancedTensor.projection sphereSequence.{u} E X ≫ (internalHomUncurry f).hom =
      E.X ◁ f.hom ≫ internalHomEvaluation E F :=
  MonoidalModuleInternalHom.projection_uncurryModule sphereSequence.{u} E f

end SerrePositivity.SymmetricSpectrum
