module

public import SerrePositivity.Spectra.SymmetricSequence.FreePairConvolution
public import SerrePositivity.Spectra.General.TensorFreeAtSum
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # 自由スペクトルのテンソル積と和次数の自由生成

F_m XとF_n Yの球面上のテンソル積をF_(m+n)(X⊗Y)へ比較する。
入力のテンソル積は基点付き単体的集合の通常のsmashである。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- F_m XとF_n Yの積は、和次数からXとYのsmashを生成する自由スペクトルと同型。 -/
abbrev sphereTensorFreeAtSum := GeneralSymmetricSpectrum.tensorFreeAtSum (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
