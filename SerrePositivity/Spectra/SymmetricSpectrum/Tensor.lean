module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.BalancedTensor
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorQuotient

/-! # 球面上の対称スペクトルのテンソル積

釣り合い商上へ球面作用を降ろし、対称スペクトルとその二変数関手を構成する。
テンソル単位・結合子・対称性の登録は次の段階で行う。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 釣り合い商へ球面作用を降ろした、球面上のテンソル積。 -/
def sphereTensor (E F : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.moduleObj sphereSequence.{u} E F

/-- 球面上のテンソル積の基礎対称列は既存の釣り合い商。 -/
lemma sphereTensor_underlying (E F : SymmetricSpectrum.{u}) :
    (sphereTensor E F).X = tensorSequence E F := rfl

/-- テンソル積の球面作用は、標準射を介して第一因子の球面作用と両立する。 -/
@[reassoc] lemma tensorProjection_action (E F : SymmetricSpectrum.{u}) :
    sphereSequence.{u} ◁ tensorProjection E F ≫ action (sphereTensor E F) =
      (α_ sphereSequence.{u} E.X F.X).inv ≫ action E ▷ F.X ≫ tensorProjection E F :=
  MonoidalBalancedTensor.projection_action sphereSequence.{u} E F

/-- 二つのスペクトルの射が誘導する、球面上のテンソル積の射。 -/
def sphereTensorMap {E E' F F' : SymmetricSpectrum.{u}} (f : E ⟶ E') (g : F ⟶ F') :
    sphereTensor E F ⟶ sphereTensor E' F' :=
  MonoidalBalancedTensor.moduleMap sphereSequence.{u} f g

/-- テンソル積の射の基礎対称列の射は、既存の釣り合い商の射。 -/
lemma sphereTensorMap_hom {E E' F F' : SymmetricSpectrum.{u}} (f : E ⟶ E') (g : F ⟶ F') :
    (sphereTensorMap f g).hom = tensorSequenceMap f g := rfl

/-- 球面上のテンソル積をスペクトル圏の二変数関手へまとめる。 -/
def sphereTensorBifunctor :
    SymmetricSpectrum.{u} × SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.moduleBifunctor sphereSequence.{u}

/-- テンソル積の球面作用を忘れると、既存の対称列の釣り合い商の関手になる。 -/
lemma sphereTensorBifunctor_forget :
    sphereTensorBifunctor.{u} ⋙ forget = tensorSequenceBifunctor := rfl

/-- 球面上のテンソル積の射は標準射との合成で決まる。 -/
lemma sphereTensor_hom_ext {E F G : SymmetricSpectrum.{u}} (f g : sphereTensor E F ⟶ G)
    (h : tensorProjection E F ≫ f.hom = tensorProjection E F ≫ g.hom) : f = g :=
  Mod.hom_ext _ _ (tensorSequence_hom_ext f.hom g.hom h)

/-- 球面作用と両立する釣り合い射を、テンソル積からのスペクトルの射へ降ろす。 -/
def sphereTensorDesc {E F G : SymmetricSpectrum.{u}} (f : TensorBalancedMap E F G.X)
    (hf : (α_ sphereSequence.{u} E.X F.X).inv ≫ action E ▷ F.X ≫ f.val =
      sphereSequence.{u} ◁ f.val ≫ action G) : sphereTensor E F ⟶ G :=
  MonoidalBalancedTensor.moduleDesc sphereSequence.{u} f hf

/-- スペクトルの射として降下した射は、標準射上で指定された値に一致する。 -/
@[reassoc] lemma tensorProjection_sphereTensorDesc {E F G : SymmetricSpectrum.{u}}
    (f : TensorBalancedMap E F G.X)
    (hf : (α_ sphereSequence.{u} E.X F.X).inv ≫ action E ▷ F.X ≫ f.val =
      sphereSequence.{u} ◁ f.val ≫ action G) :
    tensorProjection E F ≫ (sphereTensorDesc f hf).hom = f.val :=
  tensorProjection_desc f

/-- 指定された釣り合い射のスペクトルとしての降下は一意。 -/
lemma sphereTensorDesc_unique {E F G : SymmetricSpectrum.{u}} (f : TensorBalancedMap E F G.X)
    (hf : (α_ sphereSequence.{u} E.X F.X).inv ≫ action E ▷ F.X ≫ f.val =
      sphereSequence.{u} ◁ f.val ≫ action G) (g : sphereTensor E F ⟶ G)
    (h : tensorProjection E F ≫ g.hom = f.val) : g = sphereTensorDesc f hf :=
  Mod.hom_ext _ _ (tensorDesc_unique f g.hom h)

end SerrePositivity.SymmetricSpectrum
