module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor
public import SerrePositivity.Spectra.SymmetricSpectrum.Tensor
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # 自由球面加群とのテンソル積の比較

Eと自由球面加群S⊗Xの球面上のテンソル積を、対称列E.X⊗Xへ作用を与えたスペクトルと比較する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- スペクトルの右に対称列をconvolutionし、第一因子から球面作用を与える。 -/
def tensorBySequence (E : SymmetricSpectrum.{u}) (X : PointedSymmetricSequence.{u}) :
    SymmetricSpectrum.{u} := MonoidalBalancedTensor.tensorRightObj sphereSequence.{u} E X

/-- 対称列との右テンソルの基礎対称列。 -/
lemma tensorBySequence_underlying (E : SymmetricSpectrum.{u})
    (X : PointedSymmetricSequence.{u}) : (tensorBySequence E X).X = E.X ⊗ X := rfl

/-- 対称列との右テンソルの球面作用。 -/
lemma tensorBySequence_action (E : SymmetricSpectrum.{u}) (X : PointedSymmetricSequence.{u}) :
    action (tensorBySequence E X) =
      (α_ sphereSequence.{u} E.X X).inv ≫ action E ▷ X := rfl

/-- スペクトルと対称列の射から得る、右convolutionのスペクトルの射。 -/
def tensorBySequenceMap {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E')
    {X Y : PointedSymmetricSequence.{u}} (g : X ⟶ Y) :
    tensorBySequence E X ⟶ tensorBySequence E' Y :=
  MonoidalBalancedTensor.tensorRightMap sphereSequence.{u} f g

/-- 自由球面加群との右テンソル積の比較同型。 -/
def sphereTensorFreeRight (E : SymmetricSpectrum.{u}) (X : PointedSymmetricSequence.{u}) :
    sphereTensor E (freeObj X) ≅ tensorBySequence E X :=
  MonoidalBalancedTensor.freeRightIso sphereSequence.{u} E X

/-- 比較の順方向は自由加群の係数をEの右作用へ移す。 -/
@[reassoc] lemma tensorProjection_freeRight (E : SymmetricSpectrum.{u})
    (X : PointedSymmetricSequence.{u}) :
    tensorProjection E (freeObj X) ≫ (sphereTensorFreeRight E X).hom.hom =
      (α_ E.X sphereSequence.{u} X).inv ≫
        ((β_ E.X sphereSequence.{u}).hom ≫ action E) ▷ X :=
  MonoidalBalancedTensor.projection_freeRightHom sphereSequence.{u} E X

/-- 比較の逆方向は自由球面加群の生成元を挿入する。 -/
lemma sphereTensorFreeRight_inv (E : SymmetricSpectrum.{u})
    (X : PointedSymmetricSequence.{u}) :
    (sphereTensorFreeRight E X).inv.hom = E.X ◁ generator X ≫
      tensorProjection E (freeObj X) := rfl

/-- 比較同型はスペクトルと生成対称列の両方に関して自然。 -/
lemma sphereTensorFreeRight_naturality {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E')
    {X Y : PointedSymmetricSequence.{u}} (g : X ⟶ Y) :
    sphereTensorMap f (freeFunctor.map g) ≫ (sphereTensorFreeRight E' Y).hom =
      (sphereTensorFreeRight E X).hom ≫ tensorBySequenceMap f g :=
  MonoidalBalancedTensor.freeRight_naturality sphereSequence.{u} f g

/-- 自由球面加群を第二因子とするテンソル積の二変数関手。 -/
def sphereTensorFreeRightBifunctor :
    SymmetricSpectrum.{u} × PointedSymmetricSequence.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.freeRightBifunctor sphereSequence.{u}

/-- スペクトルと対称列の右convolutionの二変数関手。 -/
def tensorBySequenceBifunctor :
    SymmetricSpectrum.{u} × PointedSymmetricSequence.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.tensorRightBifunctor sphereSequence.{u}

/-- 自由球面加群との比較を二変数の自然同型へまとめる。 -/
def sphereTensorFreeRightNatIso :
    sphereTensorFreeRightBifunctor.{u} ≅ tensorBySequenceBifunctor.{u} :=
  MonoidalBalancedTensor.freeRightNatIso sphereSequence.{u}

/-- 第n段を生成する自由スペクトルとの右テンソル積の比較。 -/
def sphereTensorFreeAtRight (E : SymmetricSpectrum.{u}) (n : ℕ)
    (X : PointedSimplicialSet.{u}) :
    sphereTensor E ((freeAt n).obj X) ≅
      tensorBySequence E ((SymmetricSequence.freeAt n).obj X) :=
  sphereTensorFreeRight E ((SymmetricSequence.freeAt n).obj X)

/-- 第n段からの自由スペクトルとの比較も両方の入力に関して自然。 -/
lemma sphereTensorFreeAtRight_naturality {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E')
    (n : ℕ) {X Y : PointedSimplicialSet.{u}} (g : X ⟶ Y) :
    sphereTensorMap f ((freeAt n).map g) ≫ (sphereTensorFreeAtRight E' n Y).hom =
      (sphereTensorFreeAtRight E n X).hom ≫
        tensorBySequenceMap f ((SymmetricSequence.freeAt n).map g) :=
  sphereTensorFreeRight_naturality f ((SymmetricSequence.freeAt n).map g)

end SerrePositivity.SymmetricSpectrum
