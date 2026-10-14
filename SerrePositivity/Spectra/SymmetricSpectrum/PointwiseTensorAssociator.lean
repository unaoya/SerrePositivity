module

public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeAtSum
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.CategoryTheory.Monoidal.TensorActionTransport

/-! # 各段のsmashによる作用の結合比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 第0段の自由生成は二つの入力のsmashをスペクトルのsmashへ比較できる。 -/
def freeZeroTensorIso (X Y : PointedSimplicialSet.{u}) :
    ((freeAt 0).obj X ⊗ (freeAt 0).obj Y) ≅ (freeAt 0).obj (X ⊗ Y) :=
  sphereTensorFreeAtSum 0 0 X Y

/-- 各段のsmashを持つテンソルの反復と入力のsmashの自然比較。 -/
def pointwiseTensorAssociatorNatIso (X Y : PointedSimplicialSet.{u}) :
    pointwiseTensorFunctor (X ⊗ Y) ≅ pointwiseTensorFunctor Y ⋙ pointwiseTensorFunctor X :=
  TensorActionTransport.associatorNatIso (freeAt.{u} 0) pointwiseTensorBifunctor.{u}
    sphereTensorFreeZeroPointwiseBifunctorIso.{u} freeZeroTensorIso.{u} X Y

/-- 各段のsmashによる作用の結合同型。 -/
def pointwiseTensorAssociator (X Y : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensor (X ⊗ Y) E ≅ pointwiseTensor X (pointwiseTensor Y E) :=
  (pointwiseTensorAssociatorNatIso X Y).app E

/-- 作用の結合比較は値域スペクトルに関して自然。 -/
@[reassoc]
lemma pointwiseTensorAssociator_naturality (X Y : PointedSimplicialSet.{u})
    {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    (pointwiseTensorFunctor (X ⊗ Y)).map f ≫ (pointwiseTensorAssociator X Y F).hom =
      (pointwiseTensorAssociator X Y E).hom ≫
        (pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Y).map f) :=
  (pointwiseTensorAssociatorNatIso X Y).hom.naturality f

/-- 作用の結同比較の生成対象の両変数に関する自然性の法則。 -/
def pointwiseTensorAssociatorParameterLaw {X X' Y Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (E : SymmetricSpectrum.{u}) : Prop :=
  TensorActionTransport.associatorParameterLaw (freeAt.{u} 0) pointwiseTensorBifunctor.{u}
    sphereTensorFreeZeroPointwiseBifunctorIso.{u} freeZeroTensorIso.{u} f g E

/-- 作用の結同比較は生成対象の両変数に関しても自然。 -/
lemma pointwiseTensorAssociator_parameter_naturality
    {X X' Y Y' : PointedSimplicialSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (E : SymmetricSpectrum.{u}) : pointwiseTensorAssociatorParameterLaw f g E :=
  TensorActionTransport.associator_parameter_naturality_of_hom
    (freeAt.{u} 0) pointwiseTensorBifunctor.{u}
    sphereTensorFreeZeroPointwiseBifunctorIso.{u} freeZeroTensorIso.{u} f g E
    (sphereTensorFreeAtSum_naturality 0 0 f g)

/-- 作用の結同比較の三変数に関する自然性の法則。 -/
def pointwiseTensorAssociatorNaturalityLaw {X X' Y Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') {E F : SymmetricSpectrum.{u}} (h : E ⟶ F) : Prop :=
  TensorActionTransport.associatorNaturalityLaw (freeAt.{u} 0) pointwiseTensorBifunctor.{u}
    sphereTensorFreeZeroPointwiseBifunctorIso.{u} freeZeroTensorIso.{u} f g h

/-- 作用の結同比較は生成対象と値域スペクトルの三変数に関して自然。 -/
lemma pointwiseTensorAssociator_naturality_all
    {X X' Y Y' : PointedSimplicialSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    {E F : SymmetricSpectrum.{u}} (h : E ⟶ F) :
    pointwiseTensorAssociatorNaturalityLaw f g h :=
  TensorActionTransport.associator_naturality (freeAt.{u} 0) pointwiseTensorBifunctor.{u}
    sphereTensorFreeZeroPointwiseBifunctorIso.{u} freeZeroTensorIso.{u} f g h
    (sphereTensorFreeAtSum_naturality 0 0 f g)

end SerrePositivity.SymmetricSpectrum
