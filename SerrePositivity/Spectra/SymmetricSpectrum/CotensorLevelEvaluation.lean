module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleEvaluation
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLeftUncurry
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorAdjunction

/-! # 各段のテンソル比較の下でのcotensorの評価 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段の逆比較の下でcotensorの評価が通常の内部Homの評価になるという法則。 -/
def cotensorEvaluationLevelLaw (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u})
    (q : ℕ) : Prop :=
  SymmetricSequence.freeZeroModuleEvaluationLevelLaw sphereSequence.{u} X
    (Iso.refl (cotensor X E).X) q (cotensorEvaluation X E)

/-- 随伴の余単位としてのcotensorの評価は各段の通常の内部Homの評価法則を満たす。 -/
lemma cotensorEvaluation_level (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u})
    (q : ℕ) : cotensorEvaluationLevelLaw X E q := by
  unfold cotensorEvaluationLevelLaw
  rw [cotensorEvaluation_formula]
  apply SymmetricSequence.freeZeroUncurryModule_levelLaw
  simp only [Iso.refl_hom, Category.id_comp]
  exact internalHomCotensorIso_inv_freeHom X E

end SerrePositivity.SymmetricSpectrum
