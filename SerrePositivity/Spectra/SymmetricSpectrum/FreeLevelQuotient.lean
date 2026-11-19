module

public import SerrePositivity.Spectra.General.FreeLevelQuotient
public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotient
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLevelAction

/-! # 自由な円周スペクトルのブロック商表示

一般の比較同型と商の生成元について、座標を円周に固定する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open SerrePositivity.PointedSimplicialSet

/-- 全単射の添字に対応する、ブロック商の生成元。 -/
abbrev freeAtLevelBlockGenerator := GeneralSymmetricSpectrum.freeAtLevelBlockGenerator (K := circle.{u})

/-- 自由スペクトルの第m段と、球面側のブロック作用で割った余等化子との比較。 -/
abbrev freeAtLevelIsoBlockQuotient := GeneralSymmetricSpectrum.freeAtLevelIsoBlockQuotient (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
