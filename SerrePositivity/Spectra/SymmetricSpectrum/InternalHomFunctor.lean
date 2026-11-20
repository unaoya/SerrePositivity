module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.Spectra.SymmetricSpectrum.Closed

/-! # 内部Homの反変関手性と球面との比較 -/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 原変数のスペクトル射による内部Homの前合成。 -/
def internalHomPre {E E' : SymmetricSpectrum.{u}} (f : E' ⟶ E)
    (F : SymmetricSpectrum.{u}) : internalHom E F ⟶ internalHom E' F :=
  MonoidalModuleInternalHom.preMap sphereSequence.{u} f F

/-- 原変数に反変、値域に共変の内部Homの射。 -/
def internalHomMap {E E' F F' : SymmetricSpectrum.{u}} (f : E' ⟶ E) (g : F ⟶ F') :
    internalHom E F ⟶ internalHom E' F' :=
  MonoidalModuleInternalHom.homMap sphereSequence.{u} f g

@[simp]
lemma internalHomPre_id (E F : SymmetricSpectrum.{u}) :
    internalHomPre (𝟙 E) F = 𝟙 (internalHom E F) :=
  MonoidalModuleInternalHom.preMap_id sphereSequence.{u} E F

@[reassoc (attr := simp)]
lemma internalHomPre_comp {E₁ E₂ E₃ : SymmetricSpectrum.{u}}
    (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (F : SymmetricSpectrum.{u}) :
    internalHomPre (f ≫ g) F = internalHomPre g F ≫ internalHomPre f F :=
  MonoidalModuleInternalHom.preMap_comp sphereSequence.{u} f g F

/-- 前合成と値域の射による後合成は交換する。 -/
@[reassoc]
lemma internalHomPre_naturality {E E' F F' : SymmetricSpectrum.{u}}
    (f : E' ⟶ E) (g : F ⟶ F') :
    internalHomPre f F ≫ (internalHomFunctor E').map g =
      (internalHomFunctor E).map g ≫ internalHomPre f F' :=
  MonoidalModuleInternalHom.preMap_naturality sphereSequence.{u} f g

/-- 前合成はスペクトルとしての評価と両立する。 -/
@[reassoc]
lemma internalHomPre_evaluation {E E' : SymmetricSpectrum.{u}}
    (f : E' ⟶ E) (F : SymmetricSpectrum.{u}) :
    MonoidalBalancedTensor.moduleMap sphereSequence.{u} (𝟙 E') (internalHomPre f F) ≫
        internalHomEvaluationSpectrum E' F =
      MonoidalBalancedTensor.moduleMap sphereSequence.{u} f (𝟙 (internalHom E F)) ≫
        internalHomEvaluationSpectrum E F :=
  MonoidalModuleInternalHom.preMap_evaluation sphereSequence.{u} f F

/-- 転置は原変数の前合成とも両立する。 -/
@[reassoc]
lemma internalHomCurry_pre {E E' X F : SymmetricSpectrum.{u}}
    (f : E' ⟶ E) (g : GeneralSymmetricSpectrum.tensor E X ⟶ F) :
    internalHomCurry g ≫ internalHomPre f F =
      internalHomCurry (MonoidalBalancedTensor.moduleMap sphereSequence.{u} f (𝟙 X) ≫ g) :=
  MonoidalModuleInternalHom.curryModule_preMap sphereSequence.{u} f g

/-- 原変数に反変な内部Homの二変数関手。 -/
def internalHomBifunctor : SymmetricSpectrum.{u}ᵒᵖ ⥤
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.homBifunctor sphereSequence.{u}

/-- 二変数関手の対象は構成済みの内部Hom。 -/
lemma internalHomBifunctor_obj (E F : SymmetricSpectrum.{u}) :
    ((internalHomBifunctor.obj (Opposite.op E)).obj F) = internalHom E F := rfl

/-- 二変数関手の原変数の射は前合成。 -/
lemma internalHomBifunctor_map {E E' : SymmetricSpectrum.{u}}
    (f : E' ⟶ E) (F : SymmetricSpectrum.{u}) :
    (internalHomBifunctor.map f.op).app F = internalHomPre f F := rfl

/-- 球面からの内部Homは元のスペクトルと同型。 -/
def internalHomSphereIso (F : SymmetricSpectrum.{u}) : internalHom sphere F ≅ F :=
  MonoidalModuleInternalHom.regularHomIso sphereSequence.{u} F

/-- 球面との比較の逆射は左単位射の転置。 -/
lemma internalHomSphereIso_inv (F : SymmetricSpectrum.{u}) :
    (internalHomSphereIso F).inv =
      internalHomCurry (MonoidalBalancedTensor.leftUnitIso sphereSequence.{u} F).hom := rfl

/-- 球面との比較の順射は単位の挿入後の評価。 -/
lemma internalHomSphereIso_hom (F : SymmetricSpectrum.{u}) :
    (internalHomSphereIso F).hom =
      (MonoidalBalancedTensor.leftUnitIso sphereSequence.{u} (internalHom sphere F)).inv ≫
        internalHomEvaluationSpectrum sphere F := rfl

/-- 球面からの内部Homと元のスペクトルの比較は自然。 -/
@[reassoc]
lemma internalHomSphereIso_naturality {F G : SymmetricSpectrum.{u}} (f : F ⟶ G) :
    (internalHomFunctor sphere).map f ≫ (internalHomSphereIso G).hom =
      (internalHomSphereIso F).hom ≫ f :=
  MonoidalModuleInternalHom.regularHomIso_naturality sphereSequence.{u} f

/-- 球面からの内部Hom関手は恒等関手と自然同型。 -/
def internalHomSphereNatIso : internalHomFunctor sphere ≅ 𝟭 SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.regularHomNatIso sphereSequence.{u}

end SerrePositivity.SymmetricSpectrum
