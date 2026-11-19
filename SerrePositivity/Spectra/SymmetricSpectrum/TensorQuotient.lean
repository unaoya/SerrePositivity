module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.BalancedTensor
public import SerrePositivity.Spectra.General.Limits
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # 球面上のテンソル積の基礎となる釣り合い商

球面の二つの加群作用を同一視する余等化子を対称列の圏で構成する。
釣り合い射の降下と一意性、二変数の関手性と各段での余等化子表示を公開する。
この商上の球面作用と、スペクトル圏のモノイダル構造の登録は次に行う。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 第一のスペクトルの作用を使う、球面上のテンソル積の釣り合い関係式。 -/
def tensorRelationLeft (E F : SymmetricSpectrum.{u}) :
    (E.X ⊗ sphereSequence.{u}) ⊗ F.X ⟶ E.X ⊗ F.X :=
  MonoidalBalancedTensor.relationLeft sphereSequence.{u} E F

/-- 第二のスペクトルの作用を使う、球面上のテンソル積の釣り合い関係式。 -/
def tensorRelationRight (E F : SymmetricSpectrum.{u}) :
    (E.X ⊗ sphereSequence.{u}) ⊗ F.X ⟶ E.X ⊗ F.X :=
  MonoidalBalancedTensor.relationRight sphereSequence.{u} E F

/-- 第一の関係式はbraidingで右へ移した球面作用を使う。 -/
lemma tensorRelationLeft_eq (E F : SymmetricSpectrum.{u}) :
    tensorRelationLeft E F = ((β_ E.X sphereSequence.{u}).hom ≫ action E) ▷ F.X := rfl

/-- 第二の関係式は第二のスペクトルの球面作用を使う。 -/
lemma tensorRelationRight_eq (E F : SymmetricSpectrum.{u}) :
    tensorRelationRight E F = (α_ E.X sphereSequence.{u} F.X).hom ≫ E.X ◁ action F := rfl

/-- 球面上のテンソル積の基礎対象となる対称列。 -/
def tensorSequence (E F : SymmetricSpectrum.{u}) : PointedSymmetricSequence.{u} :=
  MonoidalBalancedTensor.obj sphereSequence.{u} E F

/-- 通常のconvolutionから、球面上の釣り合い商への標準射。 -/
def tensorProjection (E F : SymmetricSpectrum.{u}) : E.X ⊗ F.X ⟶ tensorSequence E F :=
  MonoidalBalancedTensor.projection sphereSequence.{u} E F

instance tensorProjection_epi (E F : SymmetricSpectrum.{u}) : Epi (tensorProjection E F) :=
  MonoidalBalancedTensor.projection_epi sphereSequence.{u} E F

/-- 標準射は球面の二つの作用を同一視する。 -/
@[reassoc] lemma tensorProjection_condition (E F : SymmetricSpectrum.{u}) :
    tensorRelationLeft E F ≫ tensorProjection E F =
      tensorRelationRight E F ≫ tensorProjection E F :=
  MonoidalBalancedTensor.projection_condition sphereSequence.{u} E F

/-- 球面の二つの作用に関する釣り合い条件を満たす対称列の射。 -/
def TensorBalancedMap (E F : SymmetricSpectrum.{u}) (Y : PointedSymmetricSequence.{u}) :=
  MonoidalBalancedTensor.BalancedMap sphereSequence.{u} E F Y

/-- 釣り合い条件を満たす対称列の射を商へ降ろす。 -/
def tensorDesc {E F : SymmetricSpectrum.{u}} {Y : PointedSymmetricSequence.{u}}
    (f : TensorBalancedMap E F Y) : tensorSequence E F ⟶ Y :=
  MonoidalBalancedTensor.desc sphereSequence.{u} f

/-- 降下した射は標準射上で指定された値に一致する。 -/
@[reassoc (attr := simp)] lemma tensorProjection_desc {E F : SymmetricSpectrum.{u}}
    {Y : PointedSymmetricSequence.{u}} (f : TensorBalancedMap E F Y) :
    tensorProjection E F ≫ tensorDesc f = f.val :=
  MonoidalBalancedTensor.projection_desc sphereSequence.{u} f

/-- 釣り合い射の降下は一意。 -/
lemma tensorDesc_unique {E F : SymmetricSpectrum.{u}} {Y : PointedSymmetricSequence.{u}}
    (f : TensorBalancedMap E F Y) (g : tensorSequence E F ⟶ Y)
    (h : tensorProjection E F ≫ g = f.val) : g = tensorDesc f :=
  MonoidalBalancedTensor.desc_unique sphereSequence.{u} f g h

/-- 商からの対称列の射は標準射との合成で決まる。 -/
lemma tensorSequence_hom_ext {E F : SymmetricSpectrum.{u}} {Y : PointedSymmetricSequence.{u}}
    (f g : tensorSequence E F ⟶ Y) (h : tensorProjection E F ≫ f = tensorProjection E F ≫ g) :
    f = g := MonoidalBalancedTensor.hom_ext sphereSequence.{u} f g h

/-- 商からの射と、球面の作用に関する釣り合い射との同値。 -/
def tensorSequenceHomEquiv (E F : SymmetricSpectrum.{u}) (Y : PointedSymmetricSequence.{u}) :
    (tensorSequence E F ⟶ Y) ≃ TensorBalancedMap E F Y :=
  MonoidalBalancedTensor.homEquiv sphereSequence.{u} E F Y

/-- 二つのスペクトルの射が釣り合い商へ誘導する射。 -/
def tensorSequenceMap {E E' F F' : SymmetricSpectrum.{u}} (f : E ⟶ E') (g : F ⟶ F') :
    tensorSequence E F ⟶ tensorSequence E' F' :=
  MonoidalBalancedTensor.map sphereSequence.{u} f g

/-- 商へ誘導した射はconvolution上の射と標準射を介して両立する。 -/
@[reassoc] lemma tensorProjection_map {E E' F F' : SymmetricSpectrum.{u}}
    (f : E ⟶ E') (g : F ⟶ F') :
    tensorProjection E F ≫ tensorSequenceMap f g = (f.hom ⊗ₘ g.hom) ≫ tensorProjection E' F' :=
  MonoidalBalancedTensor.projection_map sphereSequence.{u} f g

/-- 二つのスペクトルから釣り合い商の対称列を作る二変数関手。 -/
def tensorSequenceBifunctor :
    SymmetricSpectrum.{u} × SymmetricSpectrum.{u} ⥤ PointedSymmetricSequence.{u} :=
  MonoidalBalancedTensor.bifunctor sphereSequence.{u}

/-- 釣り合い商の各段は、二つの関係式の各段の余等化子。 -/
def tensorSequenceLevelIsoCoequalizer (E F : SymmetricSpectrum.{u}) (n : ℕ) :
    SymmetricSequence.level (tensorSequence E F) n ≅
      coequalizer ((tensorRelationLeft E F).app (FiniteBijection.of n))
        ((tensorRelationRight E F).app (FiniteBijection.of n)) :=
  (PreservesCoequalizer.iso (SymmetricSequence.evaluation n)
    (tensorRelationLeft E F) (tensorRelationRight E F)).symm

/-- 各段の比較同型は標準射を余等化子の標準射へ送る。 -/
@[reassoc] lemma tensorSequenceLevelIsoCoequalizer_projection (E F : SymmetricSpectrum.{u})
    (n : ℕ) :
    (tensorProjection E F).app (FiniteBijection.of n) ≫
        (tensorSequenceLevelIsoCoequalizer E F n).hom =
      coequalizer.π ((tensorRelationLeft E F).app (FiniteBijection.of n))
        ((tensorRelationRight E F).app (FiniteBijection.of n)) :=
  map_π_preserves_coequalizer_inv (SymmetricSequence.evaluation n)
    (tensorRelationLeft E F) (tensorRelationRight E F)

end SerrePositivity.SymmetricSpectrum
