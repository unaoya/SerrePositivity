module

public import SerrePositivity.CategoryTheory.FunctorTransport
public import SerrePositivity.Spectra.SymmetricSpectrum.Cotensor

/-! # cotensorの両変数関手性とF_0からの内部Homとの自然比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- cotensorの値域スペクトルに関する関手。 -/
def cotensorFunctor (X : PointedSimplicialSet.{u}) :
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  FunctorTransport.transport (GeneralSymmetricSpectrum.internalHomFunctor ((freeAt 0).obj X))
    (cotensor X) (internalHomCotensorIso X)

/-- cotensor関手の対象は構成済みのcotensorスペクトル。 -/
lemma cotensorFunctor_obj (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    (cotensorFunctor X).obj E = cotensor X E := rfl

/-- F_0からの内部Homとの比較は値域に関する自然同型。 -/
def internalHomCotensorNatIso (X : PointedSimplicialSet.{u}) :
    GeneralSymmetricSpectrum.internalHomFunctor ((freeAt 0).obj X) ≅ cotensorFunctor X :=
  FunctorTransport.iso (GeneralSymmetricSpectrum.internalHomFunctor ((freeAt 0).obj X))
    (cotensor X) (internalHomCotensorIso X)

/-- 自然比較の順成分は構成済みのスペクトルの同型。 -/
lemma internalHomCotensorNatIso_hom_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomCotensorNatIso X).hom.app E = (internalHomCotensorIso X E).hom := rfl

/-- 自然比較の逆成分も構成済みのスペクトルの逆同型。 -/
lemma internalHomCotensorNatIso_inv_app (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomCotensorNatIso X).inv.app E = (internalHomCotensorIso X E).inv := rfl

/-- 生成対象の反変な変化も含むcotensorの二変数関手。 -/
def cotensorBifunctor : PointedSimplicialSet.{u}ᵒᵖ ⥤
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  FunctorTransport.transport ((freeAt 0).op ⋙ internalHomBifunctor)
    (fun X => cotensorFunctor X.unop) (fun X => internalHomCotensorNatIso X.unop)

/-- F_0からの内部Homとの比較は生成対象と値域の両変数に関して自然。 -/
def internalHomCotensorBifunctorIso :
    (freeAt 0).op ⋙ internalHomBifunctor ≅ cotensorBifunctor :=
  FunctorTransport.iso ((freeAt 0).op ⋙ internalHomBifunctor)
    (fun X => cotensorFunctor X.unop) (fun X => internalHomCotensorNatIso X.unop)

/-- 二変数の比較の生成対象成分は値域関手の自然比較。 -/
lemma internalHomCotensorBifunctorIso_hom_app (X : PointedSimplicialSet.{u}) :
    internalHomCotensorBifunctorIso.hom.app (Opposite.op X) =
      (internalHomCotensorNatIso X).hom := rfl

/-- 二変数関手の対象はcotensor。 -/
lemma cotensorBifunctor_obj (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    (cotensorBifunctor.obj (Opposite.op X)).obj E = cotensor X E := rfl

/-- 生成対象に反変、値域に共変なcotensorのスペクトル射。 -/
def cotensorMap {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : E ⟶ F) : cotensor Y E ⟶ cotensor X F :=
  (cotensorBifunctor.map f.op).app E ≫ (cotensorFunctor X).map g

/-- cotensorの値域の射は内部Homの射を比較の順逆で移した射。 -/
lemma cotensorFunctor_map (X : PointedSimplicialSet.{u}) {E F : SymmetricSpectrum.{u}}
    (g : E ⟶ F) :
    (cotensorFunctor X).map g =
      (internalHomCotensorIso X E).inv ≫ (GeneralSymmetricSpectrum.internalHomFunctor ((freeAt 0).obj X)).map g ≫
        (internalHomCotensorIso X F).hom := rfl

end SerrePositivity.SymmetricSpectrum
