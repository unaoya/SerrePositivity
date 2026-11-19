module

public import SerrePositivity.Spectra.General.Basic
public import SerrePositivity.Spectra.SymmetricSequence.SphereCommMonoid

/-! # 円周を座標とする対称スペクトル

基礎圏を基点付き単体集合に取る。対象・射・球面の作用は一般の対称スペクトルから得る。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity
/-- 球面対称列のモノイド上の内部加群としての対称スペクトル。 -/
abbrev SymmetricSpectrum :=
  GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle

namespace SymmetricSpectrum

open PointedSimplicialSet
/-- 球面の加群作用を忘れる関手。 -/
abbrev forget := GeneralSymmetricSpectrum.forget circle.{u}

end SymmetricSpectrum
end SerrePositivity
