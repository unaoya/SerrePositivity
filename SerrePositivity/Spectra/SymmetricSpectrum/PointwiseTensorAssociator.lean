module

public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeAtSum
public import Mathlib.CategoryTheory.Whiskering

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
  (sphereTensorFreeZeroPointwiseNatIso (X ⊗ Y)).symm ≪≫
    (curriedTensor SymmetricSpectrum.{u}).mapIso (freeZeroTensorIso X Y).symm ≪≫
      tensorLeftTensor ((freeAt 0).obj X) ((freeAt 0).obj Y) ≪≫
        CategoryTheory.Functor.isoWhiskerRight (sphereTensorFreeZeroPointwiseNatIso Y)
          (tensorLeft ((freeAt 0).obj X)) ≪≫
            CategoryTheory.Functor.isoWhiskerLeft (pointwiseTensorFunctor Y)
              (sphereTensorFreeZeroPointwiseNatIso X)

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

end SerrePositivity.SymmetricSpectrum
