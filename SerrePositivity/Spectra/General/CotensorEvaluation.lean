module

public import SerrePositivity.Spectra.General.CotensorStructure
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorEvaluation
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleEvaluation

/-! # Evaluation and transposition on cotensor levels -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- cotensorの評価は全体の比較の逆射の逆転置。 -/
lemma cotensorEvaluation_formula (X : C) (E : GeneralSymmetricSpectrum C K) :
    (freeZeroTensorCotensorAdjunction X).counit.app E =
      MonoidalModuleInternalHom.uncurryModule (SymmetricSequence.tensorPowerSequence K)
        _ (internalHomCotensorIso X E).inv := by
  rw [← Adjunction.homEquiv_symm_id]
  unfold freeZeroTensorCotensorAdjunction
  erw [Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  rw [Category.id_comp]
  exact congrArg (fun e => e.symm (internalHomCotensorIso X E).inv)
    (MonoidalModuleInternalHom.adjunction_homEquiv (SymmetricSequence.tensorPowerSequence K)
      ((freeAt (K := K) 0).obj X)
      (cotensor X E) E)

/-- 随伴の余単位としてのcotensorの評価は各段の通常の内部Homの評価法則を満たす。 -/
lemma cotensorEvaluation_level (X : C) (E : GeneralSymmetricSpectrum C K)
    (q : ℕ) :
    SymmetricSequence.freeZeroModuleEvaluationLevelLaw (SymmetricSequence.tensorPowerSequence K) X
      (Iso.refl (cotensor X E).X) q ((freeZeroTensorCotensorAdjunction X).counit.app E) := by
  rw [cotensorEvaluation_formula]
  apply SymmetricSequence.freeZeroUncurryModule_levelLaw
  simp only [Iso.refl_hom, Category.id_comp]
  exact internalHomCotensorIso_inv_freeHom X E

/-- テンソルとcotensorの随伴の余単位は各段の通常の内部Homの評価法則を満たす。 -/
lemma pointwiseTensorEvaluation_level (X : C)
    (E : GeneralSymmetricSpectrum C K) (q : ℕ) :
    SymmetricSequence.pointwiseTensorEvaluationLevelLaw (SymmetricSequence.tensorPowerSequence K) X
      (Iso.refl (cotensor X E).X) q ((pointwiseTensorCotensorAdjunction X).counit.app E) :=
  SymmetricSequence.pointwiseTensorEvaluationLevelLaw_of_freeZero
    (SymmetricSequence.tensorPowerSequence K) X
    (Iso.refl (cotensor X E).X) q ((freeZeroTensorCotensorAdjunction X).counit.app E)
    ((pointwiseTensorCotensorAdjunction X).counit.app E)
    rfl (cotensorEvaluation_level X E q)

/-- スペクトルの逆転置は各段の通常の内部Homの逆転置の法則を満たす。 -/
lemma pointwiseTensorUncurry_level (X : C)
    {A E : GeneralSymmetricSpectrum C K} (f : A ⟶ cotensor X E) (q : ℕ) :
    SymmetricSequence.pointwiseTensorUncurryLevelLaw (SymmetricSequence.tensorPowerSequence K) X
      (Iso.refl (cotensor X E).X) f (((pointwiseTensorCotensorAdjunction X).homEquiv A E).symm f) q :=
  SymmetricSequence.pointwiseTensorUncurryLevelLaw_of_evaluation
    (SymmetricSequence.tensorPowerSequence K) X
    (Iso.refl (cotensor X E).X) f (((pointwiseTensorCotensorAdjunction X).homEquiv _ _).symm f)
    ((pointwiseTensorCotensorAdjunction X).counit.app E) q
    ((pointwiseTensorCotensorAdjunction X).homEquiv_symm_apply A E f)
    (pointwiseTensorEvaluation_level X E q)

/-- スペクトルの転置は各段の通常の内部Homの転置の法則を満たす。 -/
lemma pointwiseTensorCurry_level (X : C)
    {A E : GeneralSymmetricSpectrum C K} (f : pointwiseTensor X A ⟶ E) (q : ℕ) :
    SymmetricSequence.pointwiseTensorCurryLevelLaw (SymmetricSequence.tensorPowerSequence K) X
      (Iso.refl (cotensor X E).X) f ((pointwiseTensorCotensorAdjunction X).homEquiv A E f) q := by
  let e := (pointwiseTensorCotensorAdjunction X).homEquiv A E
  apply SymmetricSequence.pointwiseTensorCurryLevelLaw_of_uncurry
  have h := pointwiseTensorUncurry_level X (e f) q
  change (e.symm (e f)).hom.app (FiniteBijection.of q) = _ at h
  change f.hom.app (FiniteBijection.of q) = _
  rw [e.symm_apply_apply f] at h
  exact h

end SerrePositivity.GeneralSymmetricSpectrum
