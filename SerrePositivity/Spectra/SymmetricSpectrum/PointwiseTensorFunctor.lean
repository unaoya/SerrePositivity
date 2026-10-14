module

public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensor

/-! # 各段のsmashを持つテンソルの二変数関手性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段のsmashを持つテンソルは生成対象と値域スペクトルに共変な二変数関手。 -/
def pointwiseTensorBifunctor : PointedSimplicialSet.{u} ⥤
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  FunctorTransport.transport ((freeAt 0) ⋙ curriedTensor SymmetricSpectrum.{u})
    pointwiseTensorFunctor sphereTensorFreeZeroPointwiseNatIso

/-- F_0とのテンソル積からの比較は両変数に関する自然同型。 -/
def sphereTensorFreeZeroPointwiseBifunctorIso :
    (freeAt 0) ⋙ curriedTensor SymmetricSpectrum.{u} ≅ pointwiseTensorBifunctor :=
  FunctorTransport.iso ((freeAt 0) ⋙ curriedTensor SymmetricSpectrum.{u})
    pointwiseTensorFunctor sphereTensorFreeZeroPointwiseNatIso

/-- 二変数関手の生成対象成分は構成済みの値域関手。 -/
lemma pointwiseTensorBifunctor_obj (X : PointedSimplicialSet.{u}) :
    pointwiseTensorBifunctor.obj X = pointwiseTensorFunctor X := rfl

/-- 両変数の自然比較の各成分は構成済みのスペクトル全体の比較。 -/
lemma sphereTensorFreeZeroPointwiseBifunctorIso_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (sphereTensorFreeZeroPointwiseBifunctorIso.app X).app E =
      sphereTensorFreeZeroPointwiseIso X E := rfl

/-- 両変数の射から各段のsmashを持つスペクトルの射を構成する。 -/
def pointwiseTensorMap {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    pointwiseTensor X E ⟶ pointwiseTensor Y F :=
  (pointwiseTensorBifunctor.map f).app E ≫ (pointwiseTensorFunctor Y).map g

/-- 二変数の射は、球面上のテンソルの射を全体の比較の順逆で移した射。 -/
lemma pointwiseTensorMap_conjugate {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    (sphereTensorFreeZeroPointwiseIso X E).inv ≫
        ((freeAt 0).map f ▷ E) ≫ (tensorLeft ((freeAt 0).obj Y)).map g ≫
          (sphereTensorFreeZeroPointwiseIso Y F).hom = pointwiseTensorMap f g :=
  FunctorTransport.bimap_conjugate sphereTensorFreeZeroPointwiseBifunctorIso f g

/-- 全体の比較は両変数の射と両立する。 -/
@[reassoc]
lemma sphereTensorFreeZeroPointwiseIso_naturality
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) :
    ((freeAt 0).map f ▷ E) ≫ (tensorLeft ((freeAt 0).obj Y)).map g ≫
        (sphereTensorFreeZeroPointwiseIso Y F).hom =
      (sphereTensorFreeZeroPointwiseIso X E).hom ≫ pointwiseTensorMap f g := by
  exact FunctorTransport.bimap_naturality sphereTensorFreeZeroPointwiseBifunctorIso f g

end SerrePositivity.SymmetricSpectrum
