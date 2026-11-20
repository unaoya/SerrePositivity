module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAdjunction

/-! # 生成対象の射に関するテンソルとcotensorの転置の自然性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor pointwiseTensorPost tensorFreeZeroPointwiseIso)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 生成対象の射によるcotensorの前合成。 -/
def cotensorPre {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) : cotensor Y E ⟶ cotensor X E :=
  (cotensorBifunctor.map f.op).app E

/-- 内部Homとの比較は生成対象の前合成と両立する。 -/
@[reassoc]
lemma internalHomCotensorIso_pre {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) :
    internalHomPre ((freeAt 0).map f) E ≫ (internalHomCotensorIso X E).hom =
      (internalHomCotensorIso Y E).hom ≫ cotensorPre f E := by
  have h := congrArg (fun k => k.app E) (internalHomCotensorBifunctorIso.hom.naturality f.op)
  exact h

/-- F_0とのテンソル積の転置は生成対象の射に関して自然。 -/
lemma cotensorCurry_pre {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {A E : SymmetricSpectrum.{u}} (g : GeneralSymmetricSpectrum.tensor ((freeAt 0).obj Y) A ⟶ E) :
    cotensorCurry X (((freeAt 0).map f ▷ A) ≫ g) =
      cotensorCurry Y g ≫ cotensorPre f E := by
  have h := internalHomCurry_pre ((freeAt 0).map f) g
  have ht : MonoidalBalancedTensor.moduleMap sphereSequence.{u} ((freeAt 0).map f) (𝟙 A) =
      (freeAt 0).map f ▷ A :=
    tensorHom_id ((freeAt 0).map f) A
  rw [ht] at h
  rw [cotensorCurry_formula, cotensorCurry_formula]
  erw [← h, Category.assoc, internalHomCotensorIso_pre]
  exact (Category.assoc _ _ _).symm

/-- 各段のsmashを持つテンソルの転置は生成対象の射に関して自然。 -/
lemma pointwiseTensorCurry_post {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {A E : SymmetricSpectrum.{u}} (g : pointwiseTensor Y A ⟶ E) :
    ((pointwiseTensorCotensorAdjunction X).homEquiv _ _) (pointwiseTensorPost f A ≫ g) =
      ((pointwiseTensorCotensorAdjunction Y).homEquiv _ _) g ≫ cotensorPre f E := by
  change (((freeZeroTensorCotensorAdjunction X).ofNatIsoLeft
    (sphereTensorFreeZeroPointwiseNatIso X)).homEquiv A E) (pointwiseTensorPost f A ≫ g) =
      (((freeZeroTensorCotensorAdjunction Y).ofNatIsoLeft
        (sphereTensorFreeZeroPointwiseNatIso Y)).homEquiv A E) g ≫ cotensorPre f E
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.homEquiv_ofNatIsoLeft_apply]
  change cotensorCurry X ((tensorFreeZeroPointwiseIso X A).hom ≫ pointwiseTensorPost f A ≫ g) =
    cotensorCurry Y ((tensorFreeZeroPointwiseIso Y A).hom ≫ g) ≫ cotensorPre f E
  rw [← Category.assoc, ← GeneralSymmetricSpectrum.tensorFreeZeroPointwiseIso_post,
    Category.assoc, cotensorCurry_pre]

/-- 逆転置も生成対象の前合成と両立する。 -/
lemma pointwiseTensorUncurry_pre {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {A E : SymmetricSpectrum.{u}} (g : A ⟶ cotensor Y E) :
    ((pointwiseTensorCotensorAdjunction X).homEquiv _ _).symm (g ≫ cotensorPre f E) =
      pointwiseTensorPost f A ≫ ((pointwiseTensorCotensorAdjunction Y).homEquiv _ _).symm g := by
  apply ((pointwiseTensorCotensorAdjunction X).homEquiv A E).injective
  rw [Equiv.apply_symm_apply, pointwiseTensorCurry_post, Equiv.apply_symm_apply]

/-- cotensorの前合成と生成対象のテンソル射は評価に関して両立する。 -/
@[reassoc]
lemma pointwiseTensorEvaluation_pre {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) :
    (pointwiseTensorFunctor X).map (cotensorPre f E) ≫ (pointwiseTensorCotensorAdjunction X).counit.app E =
      pointwiseTensorPost f (cotensor Y E) ≫ (pointwiseTensorCotensorAdjunction Y).counit.app E := by
  have h := pointwiseTensorUncurry_pre f (𝟙 (cotensor Y E))
  rw [Category.id_comp] at h
  calc
    _ = ((pointwiseTensorCotensorAdjunction X).homEquiv _ _).symm (cotensorPre f E) :=
      ((pointwiseTensorCotensorAdjunction X).homEquiv_symm_apply
        (cotensor Y E) E (cotensorPre f E)).symm
    _ = pointwiseTensorPost f (cotensor Y E) ≫
        ((pointwiseTensorCotensorAdjunction Y).homEquiv _ _).symm (𝟙 (cotensor Y E)) := h
    _ = _ := congrArg (fun k => pointwiseTensorPost f (cotensor Y E) ≫ k)
      ((pointwiseTensorCotensorAdjunction Y).homEquiv_symm_id E)

end SerrePositivity.SymmetricSpectrum
