module

public import SerrePositivity.Spectra.General.ShiftedHom
public import SerrePositivity.Spectra.SymmetricSpectrum.Suspension
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomShiftEvaluation

/-! # 円周を座標とする構造射の対称列表示 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action level structureMap)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- スペクトルの構造射は一般のconvolutionの次数成分に一致する。 -/
lemma structureMap_eq_convolutionComponent (E : SymmetricSpectrum.{u}) (p q : ℕ) :
    structureMap E p q =
      SymmetricSequence.convolutionComponent (action E)
        (FiniteBijection.of p) (FiniteBijection.of q) := by
  rfl

end SerrePositivity.SymmetricSpectrum
