module

public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorAdjunction

/-! # 各段のsmashを持つテンソルとcotensorの随伴 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段の通常のsmashを持つテンソルはcotensor関手の左随伴。 -/
def pointwiseTensorCotensorAdjunction (X : PointedSimplicialSet.{u}) :
    pointwiseTensorFunctor X ⊣ cotensorFunctor X :=
  (freeZeroTensorCotensorAdjunction X).ofNatIsoLeft (sphereTensorFreeZeroPointwiseNatIso X)

/-- 各段のsmashを持つテンソルからの射とcotensorへの射の自然なHom同値。 -/
def pointwiseTensorHomEquiv (X : PointedSimplicialSet.{u}) (A E : SymmetricSpectrum.{u}) :
    (pointwiseTensor X A ⟶ E) ≃ (A ⟶ cotensor X E) :=
  (pointwiseTensorCotensorAdjunction X).homEquiv A E

/-- 各段のsmashを持つテンソルからのスペクトル射の転置。 -/
def pointwiseTensorCurry (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : pointwiseTensor X A ⟶ E) : A ⟶ cotensor X E := pointwiseTensorHomEquiv X A E f

/-- cotensorへのスペクトル射の各段のsmashを持つテンソルからの逆転置。 -/
def pointwiseTensorUncurry (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : A ⟶ cotensor X E) : pointwiseTensor X A ⟶ E :=
  (pointwiseTensorHomEquiv X A E).symm f

/-- 転置はF_0との比較の順射による前合成の既存の転置。 -/
lemma pointwiseTensorCurry_formula (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : pointwiseTensor X A ⟶ E) :
    pointwiseTensorCurry X f = cotensorCurry X ((sphereTensorFreeZeroPointwiseIso X A).hom ≫ f) :=
  Adjunction.homEquiv_ofNatIsoLeft_apply (freeZeroTensorCotensorAdjunction X)
    (sphereTensorFreeZeroPointwiseNatIso X) f

/-- 逆転置は既存の逆転置へのF_0との比較の逆射による前合成。 -/
lemma pointwiseTensorUncurry_formula (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : A ⟶ cotensor X E) :
    pointwiseTensorUncurry X f =
      (sphereTensorFreeZeroPointwiseIso X A).inv ≫ cotensorUncurry X f :=
  Adjunction.homEquiv_ofNatIsoLeft_symm_apply (freeZeroTensorCotensorAdjunction X)
    (sphereTensorFreeZeroPointwiseNatIso X) f

/-- 転置して逆転置すると元のスペクトル射になる。 -/
@[simp]
lemma pointwiseTensorUncurry_curry (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : pointwiseTensor X A ⟶ E) :
    pointwiseTensorUncurry X (pointwiseTensorCurry X f) = f :=
  (pointwiseTensorHomEquiv X A E).left_inv f

/-- 逆転置して転置すると元のcotensorへの射になる。 -/
@[simp]
lemma pointwiseTensorCurry_uncurry (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : A ⟶ cotensor X E) :
    pointwiseTensorCurry X (pointwiseTensorUncurry X f) = f :=
  (pointwiseTensorHomEquiv X A E).right_inv f

/-- 転置はパラメータスペクトルの射に関して自然。 -/
lemma pointwiseTensorCurry_naturality (X : PointedSimplicialSet.{u})
    {A B E : SymmetricSpectrum.{u}} (g : A ⟶ B) (f : pointwiseTensor X B ⟶ E) :
    pointwiseTensorCurry X ((pointwiseTensorFunctor X).map g ≫ f) =
      g ≫ pointwiseTensorCurry X f :=
  (pointwiseTensorCotensorAdjunction X).homEquiv_naturality_left g f

/-- 転置は値域スペクトルの射に関して自然。 -/
lemma pointwiseTensorCurry_naturality_right (X : PointedSimplicialSet.{u})
    {A E F : SymmetricSpectrum.{u}} (f : pointwiseTensor X A ⟶ E) (g : E ⟶ F) :
    pointwiseTensorCurry X (f ≫ g) =
      pointwiseTensorCurry X f ≫ (cotensorFunctor X).map g :=
  (pointwiseTensorCotensorAdjunction X).homEquiv_naturality_right f g

/-- 通常の各段のテンソルとcotensorの随伴の余単位。 -/
def pointwiseTensorEvaluation (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensor X (cotensor X E) ⟶ E :=
  (pointwiseTensorCotensorAdjunction X).counit.app E

/-- 余単位の評価は恒等射の逆転置。 -/
lemma pointwiseTensorEvaluation_uncurry (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    pointwiseTensorEvaluation X E = pointwiseTensorUncurry X (𝟙 (cotensor X E)) :=
  ((pointwiseTensorCotensorAdjunction X).homEquiv_symm_id E).symm

end SerrePositivity.SymmetricSpectrum
