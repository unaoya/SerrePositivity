module

public import SerrePositivity.Spectra.General.Evaluation
public import SerrePositivity.Spectra.SymmetricSequence.Evaluation
public import SerrePositivity.Spectra.SymmetricSpectrum.Free

/-! # 円周スペクトルの評価とその左随伴

評価・第 n 段の自由関手・随伴・生成元について、一般の構成の座標を円周に固定する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open PointedSimplicialSet

/-- スペクトルの置換作用を忘れた第n段の評価。 -/
abbrev evaluation := GeneralSymmetricSpectrum.evaluation (K := circle.{u})

/-- 基点付き単体的集合から第n段を生成する自由スペクトル関手F_n。 -/
abbrev freeAt := GeneralSymmetricSpectrum.freeAt (K := circle.{u})

/-- F_nと第n段の評価との随伴。 -/
abbrev freeAtAdjunction := GeneralSymmetricSpectrum.freeAtAdjunction (K := circle.{u})

/-- F_n Xの第n段への生成元の射。 -/
abbrev freeAtGenerator := GeneralSymmetricSpectrum.freeAtGenerator (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
