module

public import SerrePositivity.Spectra.General.Free
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere

/-! # 自由な円周スペクトル

自由加群関手と生成元の座標を円周に固定する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open SerrePositivity.PointedSimplicialSet

/-- 対称列Fを生成元とする自由球面加群。 -/
abbrev freeObj := GeneralSymmetricSpectrum.freeObj circle.{u}
/-- 対称列から自由対称スペクトルを作る関手。 -/
abbrev freeFunctor := GeneralSymmetricSpectrum.freeFunctor circle.{u}
/-- 対称列から自由対称スペクトルへの生成元の射。 -/
abbrev generator := GeneralSymmetricSpectrum.generator circle.{u}
end SerrePositivity.SymmetricSpectrum
