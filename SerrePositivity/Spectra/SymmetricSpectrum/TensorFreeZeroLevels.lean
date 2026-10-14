module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolution
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeLeft

/-! # F_0との球面上のテンソル積の各段 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- F_0 Xとの球面上のテンソル積の第q段を通常のsmashへ比較する。 -/
def sphereTensorFreeZeroLevelIso (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (sphereTensor ((freeAt 0).obj X) E) q ≅ X ⊗ level E q :=
  (evaluation q).mapIso (sphereTensorFreeAtLeft 0 X E) ≪≫
    SymmetricSequence.freeZeroConvolutionLevelIso X E.X q

end SerrePositivity.SymmetricSpectrum
