module

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

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段のsmashからの評価は比較の逆射を介した既存のcotensorの評価。 -/
lemma pointwiseTensorEvaluation_formula (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    pointwiseTensorEvaluation X E =
      (sphereTensorFreeZeroPointwiseIso X (cotensor X E)).inv ≫ cotensorEvaluation X E := by
  rw [pointwiseTensorEvaluation_uncurry, pointwiseTensorUncurry_formula]
  exact congrArg (fun h => (sphereTensorFreeZeroPointwiseIso X (cotensor X E)).inv ≫ h)
    ((freeZeroTensorCotensorAdjunction X).homEquiv_symm_id E)

/-- 各段のsmashからの評価が通常の内部Homの評価になるという法則。 -/
def pointwiseTensorEvaluationLevelLaw (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) : Prop :=
  SymmetricSequence.pointwiseTensorEvaluationLevelLaw sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) q (pointwiseTensorEvaluation X E)

/-- テンソルとcotensorの随伴の余単位は各段の通常の内部Homの評価法則を満たす。 -/
lemma pointwiseTensorEvaluation_level (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) : pointwiseTensorEvaluationLevelLaw X E q :=
  SymmetricSequence.pointwiseTensorEvaluationLevelLaw_of_freeZero sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) q (cotensorEvaluation X E) (pointwiseTensorEvaluation X E)
    (pointwiseTensorEvaluation_formula X E) (cotensorEvaluation_level X E q)

/-- 各段の逆転置が通常の内部Homの逆転置になるという法則。 -/
def pointwiseTensorUncurryLevelLaw (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : A ⟶ cotensor X E) (q : ℕ) : Prop :=
  SymmetricSequence.pointwiseTensorUncurryLevelLaw sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) f (pointwiseTensorUncurry X f) q

/-- スペクトルの逆転置は各段の通常の内部Homの逆転置の法則を満たす。 -/
lemma pointwiseTensorUncurry_level (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : A ⟶ cotensor X E) (q : ℕ) :
    pointwiseTensorUncurryLevelLaw X f q :=
  SymmetricSequence.pointwiseTensorUncurryLevelLaw_of_evaluation sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) f (pointwiseTensorUncurry X f)
    (pointwiseTensorEvaluation X E) q
    ((pointwiseTensorCotensorAdjunction X).homEquiv_symm_apply A E f)
    (pointwiseTensorEvaluation_level X E q)

/-- 各段の転置が通常の内部Homの転置になるという法則。 -/
def pointwiseTensorCurryLevelLaw (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : pointwiseTensor X A ⟶ E) (q : ℕ) : Prop :=
  SymmetricSequence.pointwiseTensorCurryLevelLaw sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) f (pointwiseTensorCurry X f) q

/-- スペクトルの転置は各段の通常の内部Homの転置の法則を満たす。 -/
lemma pointwiseTensorCurry_level (X : PointedSimplicialSet.{u})
    {A E : SymmetricSpectrum.{u}} (f : pointwiseTensor X A ⟶ E) (q : ℕ) :
    pointwiseTensorCurryLevelLaw X f q := by
  apply SymmetricSequence.pointwiseTensorCurryLevelLaw_of_uncurry
  have h := pointwiseTensorUncurry_level X (pointwiseTensorCurry X f) q
  unfold pointwiseTensorUncurryLevelLaw at h
  rw [pointwiseTensorUncurry_curry] at h
  exact h

end SerrePositivity.SymmetricSpectrum
