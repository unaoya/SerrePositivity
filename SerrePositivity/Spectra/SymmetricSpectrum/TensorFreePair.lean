module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeRight

/-! # 二つの自由スペクトルのテンソル積

自由球面加群の積を、生成対称列のconvolutionから作る自由球面加群と比較する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 自由球面加群の右convolutionを、生成対称列の積の自由球面加群へ比較する。 -/
def freeTensorBySequence (X Y : PointedSymmetricSequence.{u}) :
    tensorBySequence (freeObj X) Y ≅ freeObj (X ⊗ Y) :=
  MonoidalBalancedTensor.freeTensorIso sphereSequence.{u} X Y

/-- 二つの自由球面加群の球面上のテンソル積の比較同型。 -/
def sphereTensorFreePair (X Y : PointedSymmetricSequence.{u}) :
    sphereTensor (freeObj X) (freeObj Y) ≅ freeObj (X ⊗ Y) :=
  MonoidalBalancedTensor.freePairIso sphereSequence.{u} X Y

/-- 二つの自由球面加群の比較は、右因子の比較と結合子の合成。 -/
lemma sphereTensorFreePair_eq (X Y : PointedSymmetricSequence.{u}) :
    sphereTensorFreePair X Y =
      sphereTensorFreeRight (freeObj X) Y ≪≫ freeTensorBySequence X Y := rfl

/-- 二つの自由球面加群の比較は両方の生成対称列の射に関して自然。 -/
lemma sphereTensorFreePair_naturality {X X' Y Y' : PointedSymmetricSequence.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    sphereTensorMap (freeFunctor.map f) (freeFunctor.map g) ≫
        (sphereTensorFreePair X' Y').hom =
      (sphereTensorFreePair X Y).hom ≫ freeFunctor.map (f ⊗ₘ g) :=
  MonoidalBalancedTensor.freePair_naturality sphereSequence.{u} f g

/-- 逆比較は生成対称列の積の生成元を二つの自由スペクトルの生成元へ送る。 -/
@[reassoc] lemma generator_sphereTensorFreePair_inv (X Y : PointedSymmetricSequence.{u}) :
    generator (X ⊗ Y) ≫ (sphereTensorFreePair X Y).inv.hom =
      (generator X ⊗ₘ generator Y) ≫ tensorProjection (freeObj X) (freeObj Y) :=
  MonoidalBalancedTensor.generator_freePair_inv sphereSequence.{u} X Y

/-- 順比較は二つの自由スペクトルの生成元を積の生成元へ送る。 -/
@[reassoc] lemma generators_sphereTensorFreePair_hom (X Y : PointedSymmetricSequence.{u}) :
    (generator X ⊗ₘ generator Y) ≫ tensorProjection (freeObj X) (freeObj Y) ≫
        (sphereTensorFreePair X Y).hom.hom = generator (X ⊗ Y) :=
  MonoidalBalancedTensor.generators_freePair_hom sphereSequence.{u} X Y

/-- 二つの自由球面加群をテンソルする二変数関手。 -/
def sphereTensorFreePairBifunctor :
    PointedSymmetricSequence.{u} × PointedSymmetricSequence.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.freePairBifunctor sphereSequence.{u}

/-- 生成対称列をconvolutionして自由球面加群を作る二変数関手。 -/
def freeConvolutionBifunctor :
    PointedSymmetricSequence.{u} × PointedSymmetricSequence.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.freeProductBifunctor sphereSequence.{u}

/-- 二つの自由球面加群のテンソル積の二変数の自然比較。 -/
def sphereTensorFreePairNatIso :
    sphereTensorFreePairBifunctor.{u} ≅ freeConvolutionBifunctor.{u} :=
  MonoidalBalancedTensor.freePairNatIso sphereSequence.{u}

/-- F_mとF_nの積を、両方の生成対称列のconvolutionの自由球面加群へ比較する。 -/
def sphereTensorFreeAtPair (m n : ℕ) (X Y : PointedSimplicialSet.{u}) :
    sphereTensor ((freeAt m).obj X) ((freeAt n).obj Y) ≅
      freeObj (((SymmetricSequence.freeAt m).obj X) ⊗ ((SymmetricSequence.freeAt n).obj Y)) :=
  sphereTensorFreePair ((SymmetricSequence.freeAt m).obj X) ((SymmetricSequence.freeAt n).obj Y)

/-- F_mとF_nの積の比較は両方の基点付き単体的集合の射に関して自然。 -/
lemma sphereTensorFreeAtPair_naturality (m n : ℕ) {X X' Y Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    sphereTensorMap ((freeAt m).map f) ((freeAt n).map g) ≫
        (sphereTensorFreeAtPair m n X' Y').hom =
      (sphereTensorFreeAtPair m n X Y).hom ≫
        freeFunctor.map (((SymmetricSequence.freeAt m).map f) ⊗ₘ
          ((SymmetricSequence.freeAt n).map g)) :=
  sphereTensorFreePair_naturality ((SymmetricSequence.freeAt m).map f)
    ((SymmetricSequence.freeAt n).map g)

end SerrePositivity.SymmetricSpectrum
