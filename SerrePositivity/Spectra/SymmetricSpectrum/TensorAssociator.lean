module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.Tensor

/-! # 球面上のテンソル積の結合自然同型

三つの因子からの標準射上で基礎対称列の結合子と比較する。
pentagon・triangle・hexagonの整合性とモノイダル構造の登録は次の段階で行う。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面上の三重テンソル積の結合順を比較する同型。 -/
def sphereTensorAssociator (E F G : SymmetricSpectrum.{u}) :
    sphereTensor (sphereTensor E F) G ≅ sphereTensor E (sphereTensor F G) :=
  MonoidalBalancedTensor.associatorIso sphereSequence.{u} E F G

/-- 左結合の三重テンソル積への三つの因子からの標準射。 -/
def tensorTripleLeftProjection (E F G : SymmetricSpectrum.{u}) :
    (E.X ⊗ F.X) ⊗ G.X ⟶ (sphereTensor (sphereTensor E F) G).X :=
  MonoidalBalancedTensor.tripleLeftProjection sphereSequence.{u} E F G

/-- 右結合の三重テンソル積への三つの因子からの標準射。 -/
def tensorTripleRightProjection (E F G : SymmetricSpectrum.{u}) :
    E.X ⊗ (F.X ⊗ G.X) ⟶ (sphereTensor E (sphereTensor F G)).X :=
  MonoidalBalancedTensor.tripleRightProjection sphereSequence.{u} E F G

/-- 結合同型の順方向は三因子の標準射上で基礎対称列の結合子に一致する。 -/
@[reassoc] lemma tensorTripleLeftProjection_associator (E F G : SymmetricSpectrum.{u}) :
    tensorTripleLeftProjection E F G ≫ (sphereTensorAssociator E F G).hom.hom =
      (α_ E.X F.X G.X).hom ≫ tensorTripleRightProjection E F G :=
  MonoidalBalancedTensor.tripleLeftProjection_associatorHom sphereSequence.{u} E F G

/-- 結合同型の逆方向は三因子の標準射上で基礎対称列の結合子の逆に一致する。 -/
@[reassoc] lemma tensorTripleRightProjection_associator_inv (E F G : SymmetricSpectrum.{u}) :
    tensorTripleRightProjection E F G ≫ (sphereTensorAssociator E F G).inv.hom =
      (α_ E.X F.X G.X).inv ≫ tensorTripleLeftProjection E F G :=
  MonoidalBalancedTensor.tripleRightProjection_associatorInv sphereSequence.{u} E F G

/-- 左結合の三因子の標準射はエピ射。 -/
instance tensorTripleLeftProjection_epi (E F G : SymmetricSpectrum.{u}) :
    Epi (tensorTripleLeftProjection E F G) :=
  MonoidalBalancedTensor.tripleLeftProjection_epi sphereSequence.{u} E F G

/-- 右結合の三因子の標準射はエピ射。 -/
instance tensorTripleRightProjection_epi (E F G : SymmetricSpectrum.{u}) :
    Epi (tensorTripleRightProjection E F G) :=
  MonoidalBalancedTensor.tripleRightProjection_epi sphereSequence.{u} E F G

/-- 球面上の結合同型は三つのスペクトルの射に関して自然。 -/
lemma sphereTensorAssociator_naturality {E E' F F' G G' : SymmetricSpectrum.{u}}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    sphereTensorMap (sphereTensorMap f g) h ≫ (sphereTensorAssociator E' F' G').hom =
      (sphereTensorAssociator E F G).hom ≫ sphereTensorMap f (sphereTensorMap g h) :=
  MonoidalBalancedTensor.associator_naturality sphereSequence.{u} f g h

/-- 左結合した球面上のテンソル積の三変数関手。 -/
def sphereTensorTripleLeftFunctor :
    (SymmetricSpectrum.{u} × SymmetricSpectrum.{u}) × SymmetricSpectrum.{u} ⥤
      SymmetricSpectrum.{u} := MonoidalBalancedTensor.tripleLeftFunctor sphereSequence.{u}

/-- 右結合した球面上のテンソル積の三変数関手。 -/
def sphereTensorTripleRightFunctor :
    (SymmetricSpectrum.{u} × SymmetricSpectrum.{u}) × SymmetricSpectrum.{u} ⥤
      SymmetricSpectrum.{u} := MonoidalBalancedTensor.tripleRightFunctor sphereSequence.{u}

/-- 球面上の三重テンソル積の結合自然同型。 -/
def sphereTensorAssociatorNatIso :
    sphereTensorTripleLeftFunctor.{u} ≅ sphereTensorTripleRightFunctor.{u} :=
  MonoidalBalancedTensor.associatorNatIso sphereSequence.{u}

end SerrePositivity.SymmetricSpectrum
