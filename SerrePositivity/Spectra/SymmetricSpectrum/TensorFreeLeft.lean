module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeRight
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorSymmetry

/-! # 自由球面加群を左因子とするテンソル積

Free(X)とEの球面上の積を、対称列X⊗E.Xへ作用を与えたスペクトルと比較する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 対称列をスペクトルの左にconvolutionし、交換で移した球面作用を与える。 -/
def sequenceTensor (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} := MonoidalBalancedTensor.tensorLeftObj sphereSequence.{u} X E

/-- 左convolutionの基礎対称列。 -/
lemma sequenceTensor_underlying (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    (sequenceTensor X E).X = X ⊗ E.X := rfl

/-- 左convolutionの球面作用は右convolutionの作用を交換で移したもの。 -/
lemma sequenceTensor_action (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    action (sequenceTensor X E) = sphereSequence.{u} ◁ (β_ E.X X).inv ≫
      (α_ sphereSequence.{u} E.X X).inv ≫ action E ▷ X ≫ (β_ E.X X).hom :=
  MonoidalBalancedTensor.tensorLeftObj_action sphereSequence.{u} X E

/-- 対称列とスペクトルの射から得る左convolutionの射。 -/
def sequenceTensorMap {X Y : PointedSymmetricSequence.{u}} (g : X ⟶ Y)
    {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E') : sequenceTensor X E ⟶ sequenceTensor Y E' :=
  MonoidalBalancedTensor.tensorLeftMap sphereSequence.{u} g f

/-- 左convolutionの射の基礎射は対称列のテンソル射。 -/
lemma sequenceTensorMap_hom {X Y : PointedSymmetricSequence.{u}} (g : X ⟶ Y)
    {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E') : (sequenceTensorMap g f).hom = g ⊗ₘ f.hom :=
  MonoidalBalancedTensor.tensorLeftMap_hom sphereSequence.{u} g f

/-- 左右の対称列とのconvolutionの交換比較。 -/
def sequenceTensorIso (E : SymmetricSpectrum.{u}) (X : PointedSymmetricSequence.{u}) :
    tensorBySequence E X ≅ sequenceTensor X E :=
  MonoidalBalancedTensor.tensorLeftIso sphereSequence.{u} E X

/-- 自由球面加群を左因子とするテンソル積の比較同型。 -/
def sphereTensorFreeLeft (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    sphereTensor (freeObj X) E ≅ sequenceTensor X E :=
  MonoidalBalancedTensor.freeLeftIso sphereSequence.{u} X E

/-- 左自由因子の比較は交換・右自由因子の比較・左右convolutionの交換の合成。 -/
lemma sphereTensorFreeLeft_eq (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    sphereTensorFreeLeft X E = sphereTensorSymmetry (freeObj X) E ≪≫
      sphereTensorFreeRight E X ≪≫ sequenceTensorIso E X := rfl

/-- 左自由因子の比較は対称列とスペクトルの射の両方に関して自然。 -/
lemma sphereTensorFreeLeft_naturality {X Y : PointedSymmetricSequence.{u}} (g : X ⟶ Y)
    {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E') :
    sphereTensorMap (freeFunctor.map g) f ≫ (sphereTensorFreeLeft Y E').hom =
      (sphereTensorFreeLeft X E).hom ≫ sequenceTensorMap g f :=
  MonoidalBalancedTensor.freeLeft_naturality sphereSequence.{u} g f

/-- 左自由因子の比較の逆射は第一因子に生成元を挿入する。 -/
lemma sphereTensorFreeLeft_inv (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    (sphereTensorFreeLeft X E).inv.hom = generator X ▷ E.X ≫ tensorProjection (freeObj X) E :=
  MonoidalBalancedTensor.freeLeftIso_inv sphereSequence.{u} X E

/-- 左自由因子の比較は生成元上で恒等射となる。 -/
@[reassoc] lemma generator_sphereTensorFreeLeft (X : PointedSymmetricSequence.{u})
    (E : SymmetricSpectrum.{u}) :
    generator X ▷ E.X ≫ tensorProjection (freeObj X) E ≫ (sphereTensorFreeLeft X E).hom.hom =
      𝟙 (X ⊗ E.X) := MonoidalBalancedTensor.generator_freeLeft_hom sphereSequence.{u} X E

/-- 自由球面加群を左因子とする積の二変数関手。 -/
def sphereTensorFreeLeftBifunctor :
    PointedSymmetricSequence.{u} × SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.freeLeftBifunctor sphereSequence.{u}

/-- 対称列とスペクトルの左convolutionの二変数関手。 -/
def sequenceTensorBifunctor :
    PointedSymmetricSequence.{u} × SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.tensorLeftBifunctor sphereSequence.{u}

/-- 左自由因子の比較を二変数の自然同型へまとめる。 -/
def sphereTensorFreeLeftNatIso :
    sphereTensorFreeLeftBifunctor.{u} ≅ sequenceTensorBifunctor.{u} :=
  MonoidalBalancedTensor.freeLeftNatIso sphereSequence.{u}

/-- 第n段から生成する自由スペクトルを左因子に置く比較。 -/
def sphereTensorFreeAtLeft (n : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    sphereTensor ((freeAt n).obj X) E ≅ sequenceTensor ((SymmetricSequence.freeAt n).obj X) E :=
  sphereTensorFreeLeft ((SymmetricSequence.freeAt n).obj X) E

/-- F_nを左因子に置く比較は両方の入力の射に関して自然。 -/
lemma sphereTensorFreeAtLeft_naturality (n : ℕ) {X Y : PointedSimplicialSet.{u}} (g : X ⟶ Y)
    {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E') :
    sphereTensorMap ((freeAt n).map g) f ≫ (sphereTensorFreeAtLeft n Y E').hom =
      (sphereTensorFreeAtLeft n X E).hom ≫
        sequenceTensorMap ((SymmetricSequence.freeAt n).map g) f :=
  sphereTensorFreeLeft_naturality ((SymmetricSequence.freeAt n).map g) f

end SerrePositivity.SymmetricSpectrum
