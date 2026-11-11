module

public import SerrePositivity.KST.Spectra.SpectrumZeroObject

/-!
概要：厳密なスペクトルの零射の段ごとの計算。
方針：一点スペクトルを経由する零射を、各段の点つき零射に同定する。
規約：既存の HasZeroMorphisms の選択を保つ。使われ方：loop の厳密な零合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

@[simp]
lemma zero_app (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (0 : X ⟶ Y).app n = 0 := by
  change (point_isZero.from_ X).app n ≫ (point_isZero.to_ Y).app n = 0
  have h : (point_isZero.from_ X).app n = 0 := PointedObject.point_isZero.eq_of_tgt _ _
  rw [h, zero_comp]

end SerrePositivity.KST.Spectra.OmegaSpectrum
