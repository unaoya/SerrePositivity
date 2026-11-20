module

public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorFunctor

/-! # F_0によるテンソル積とcotensorの随伴・転置・評価 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- F_0 Xとの球面上のテンソル積はcotensor関手の左随伴。 -/
def freeZeroTensorCotensorAdjunction (X : PointedSimplicialSet.{u}) :
    tensorLeft ((freeAt 0).obj X) ⊣ cotensorFunctor X :=
  (GeneralSymmetricSpectrum.tensorInternalHomAdjunction ((freeAt 0).obj X)).ofNatIsoRight
    (internalHomCotensorNatIso X)

/-- F_0とのテンソル積からの射とcotensorへの射の自然なHom同値。 -/
def cotensorHomEquiv (X : PointedSimplicialSet.{u}) (A E : SymmetricSpectrum.{u}) :
    (GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) A ⟶ E) ≃ (A ⟶ cotensor X E) :=
  (freeZeroTensorCotensorAdjunction X).homEquiv A E

/-- F_0とのテンソル積からのスペクトル射のcotensorへの転置。 -/
def cotensorCurry (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) A ⟶ E) : A ⟶ cotensor X E :=
  cotensorHomEquiv X A E f

/-- cotensorへのスペクトル射のF_0とのテンソル積からの逆転置。 -/
def cotensorUncurry (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : A ⟶ cotensor X E) : GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) A ⟶ E :=
  (cotensorHomEquiv X A E).symm f

/-- cotensorへの転置は既存の内部Homへの転置と比較の順射の合成。 -/
lemma cotensorCurry_formula (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) A ⟶ E) :
    cotensorCurry X f = MonoidalModuleInternalHom.curryModule sphereSequence.{u} _ f ≫ (internalHomCotensorIso X E).hom := by
  unfold cotensorCurry cotensorHomEquiv freeZeroTensorCotensorAdjunction
  erw [Adjunction.homEquiv_ofNatIsoRight_apply, internalHomCotensorNatIso_hom_app]
  erw [MonoidalModuleInternalHom.adjunction_homEquiv]
  rfl

/-- cotensorからの逆転置は比較の逆射との合成を既存の内部Homで逆転置する射。 -/
lemma cotensorUncurry_formula (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : A ⟶ cotensor X E) :
    cotensorUncurry X f = MonoidalModuleInternalHom.uncurryModule sphereSequence.{u} _ (f ≫ (internalHomCotensorIso X E).inv) := by
  unfold cotensorUncurry cotensorHomEquiv freeZeroTensorCotensorAdjunction
  erw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, internalHomCotensorNatIso_inv_app]
  erw [MonoidalModuleInternalHom.adjunction_homEquiv]
  rfl

/-- 転置して逆転置すると元のスペクトル射になる。 -/
@[simp]
lemma cotensorUncurry_curry (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) A ⟶ E) :
    cotensorUncurry X (cotensorCurry X f) = f :=
  (cotensorHomEquiv X A E).left_inv f

/-- 逆転置して転置しても元のcotensorへの射になる。 -/
@[simp]
lemma cotensorCurry_uncurry (X : PointedSimplicialSet.{u}) {A E : SymmetricSpectrum.{u}}
    (f : A ⟶ cotensor X E) : cotensorCurry X (cotensorUncurry X f) = f :=
  (cotensorHomEquiv X A E).right_inv f

/-- 転置はパラメータスペクトルの射に関して自然。 -/
lemma cotensorCurry_naturality (X : PointedSimplicialSet.{u}) {A B E : SymmetricSpectrum.{u}}
    (g : A ⟶ B) (f : GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) B ⟶ E) :
    cotensorCurry X ((tensorLeft ((freeAt 0).obj X)).map g ≫ f) = g ≫ cotensorCurry X f :=
  (freeZeroTensorCotensorAdjunction X).homEquiv_naturality_left g f

/-- 転置は値域スペクトルの射に関して自然。 -/
lemma cotensorCurry_naturality_right (X : PointedSimplicialSet.{u})
    {A E F : SymmetricSpectrum.{u}}
    (f : GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) A ⟶ E) (g : E ⟶ F) :
    cotensorCurry X (f ≫ g) = cotensorCurry X f ≫ (cotensorFunctor X).map g :=
  (freeZeroTensorCotensorAdjunction X).homEquiv_naturality_right f g

/-- 随伴の余単位としてのcotensorのスペクトル評価。 -/
def cotensorEvaluation (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    GeneralSymmetricSpectrum.tensor ((freeAt 0).obj X) (cotensor X E) ⟶ E :=
  (freeZeroTensorCotensorAdjunction X).counit.app E

/-- cotensorの評価は全体の比較の逆射の逆転置。 -/
lemma cotensorEvaluation_formula (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    cotensorEvaluation X E = MonoidalModuleInternalHom.uncurryModule sphereSequence.{u} _ (internalHomCotensorIso X E).inv := by
  unfold cotensorEvaluation
  rw [← Adjunction.homEquiv_symm_id]
  change cotensorUncurry X (𝟙 (cotensor X E)) = _
  rw [cotensorUncurry_formula, Category.id_comp]

end SerrePositivity.SymmetricSpectrum
