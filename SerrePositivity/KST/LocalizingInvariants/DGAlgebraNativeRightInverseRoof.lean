module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedUpperRightRoofPath

/-!
概要：元の右三角形だけを持つ実 roof を記録し、完成済みの二切断右逆を包装する。
方針：元の分母・分子と指定した乗法的経路をそのまま保持する。
規約：左三角形は主張しない。使われ方：対角への右逆構成の再適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}

structure NativeRightInverseRoof (f : LevelHom X Y) (i m : ℕ) (hi : i ≤ m) where
  roof : SurjectiveRoof R (Y.obj m) (X.obj i)
  rightPath : Path.Witness R (roof.numerator ≫ f.app i) (roof.denominator ≫ Y.transition hi)

variable {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B} {j : ℕ}
  (d : PostnikovTwoClassInverseData R f j)

def PostnikovTwoClassInverseData.nativeRightInverseRoof :
    NativeRightInverseRoof R (f.map (postnikovFunctor R 2)) j d.layerInverse.zero.stage
      (d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)) :=
  ⟨d.nonpositiveFixedRightRoof R, d.nonpositiveFixedRightRoofPath R⟩

lemma exists_postnikovTwoNativeRightInverseRoof (f : LevelHom A B)
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1)))
    (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, Nonempty (NativeRightInverseRoof R (f.map (postnikovFunctor R 2)) i m hi) := by
  obtain ⟨d, _⟩ := exists_postnikovTwoClassInverseData_after R f h₀ h₁ h₂ i i
  exact ⟨_, _, ⟨d.nativeRightInverseRoof R⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
