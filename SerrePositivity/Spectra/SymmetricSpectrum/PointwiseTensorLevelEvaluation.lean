module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorEvaluation
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAdjunction
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorLevelEvaluation

/-! # 各段のsmashとcotensorの通常の評価・逆転置 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor tensorFreeZeroPointwiseIso)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段のsmashからの評価は比較の逆射を介した既存のcotensorの評価。 -/
lemma pointwiseTensorEvaluation_formula (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (pointwiseTensorCotensorAdjunction X).counit.app E =
      (tensorFreeZeroPointwiseIso X (cotensor X E)).inv ≫ cotensorEvaluation X E := rfl

/-- テンソルとcotensorの随伴の余単位は各段の通常の内部Homの評価法則を満たす。 -/
lemma pointwiseTensorEvaluation_level (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    SymmetricSequence.pointwiseTensorEvaluationLevelLaw sphereSequence.{u} X
      (Iso.refl (cotensor X E).X) q ((pointwiseTensorCotensorAdjunction X).counit.app E) :=
  SymmetricSequence.pointwiseTensorEvaluationLevelLaw_of_freeZero sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) q (cotensorEvaluation X E)
    ((pointwiseTensorCotensorAdjunction X).counit.app E)
    (pointwiseTensorEvaluation_formula X E) (cotensorEvaluation_level X E q)

/-- スペクトルの逆転置は各段の通常の内部Homの逆転置の法則を満たす。 -/
lemma pointwiseTensorUncurry_level (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : A ⟶ cotensor X E) (q : ℕ) :
    SymmetricSequence.pointwiseTensorUncurryLevelLaw sphereSequence.{u} X
      (Iso.refl (cotensor X E).X) f ((pointwiseTensorCotensorAdjunction X).homEquiv A E |>.symm f) q :=
  SymmetricSequence.pointwiseTensorUncurryLevelLaw_of_evaluation sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) f (((pointwiseTensorCotensorAdjunction X).homEquiv _ _).symm f)
    ((pointwiseTensorCotensorAdjunction X).counit.app E) q
    ((pointwiseTensorCotensorAdjunction X).homEquiv_symm_apply A E f)
    (pointwiseTensorEvaluation_level X E q)

/-- スペクトルの転置は各段の通常の内部Homの転置の法則を満たす。 -/
lemma pointwiseTensorCurry_level (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : pointwiseTensor X A ⟶ E) (q : ℕ) :
    SymmetricSequence.pointwiseTensorCurryLevelLaw sphereSequence.{u} X
      (Iso.refl (cotensor X E).X) f ((pointwiseTensorCotensorAdjunction X).homEquiv A E f) q := by
  let e := (pointwiseTensorCotensorAdjunction X).homEquiv A E
  apply SymmetricSequence.pointwiseTensorCurryLevelLaw_of_uncurry
  have h := pointwiseTensorUncurry_level X (e f) q
  change (e.symm (e f)).hom.app (FiniteBijection.of q) = _ at h
  change f.hom.app (FiniteBijection.of q) = _
  rw [e.symm_apply_apply f] at h
  exact h

end SerrePositivity.SymmetricSpectrum
