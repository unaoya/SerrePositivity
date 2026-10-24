module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedUpperRightRoofPath

/-!
概要：実下段逆から、任意の次段切断射の実右逆 roof を構成する。
方針：共通核の class 逆を次段の元の代数へ戻し、指定した右経路を保持する。
規約：下段逆は帰納入力。次数 n+1 と係数の単位 shift 1 を区別する。
使われ方：有限 Postnikov 帰納と、下界を持つ実代数への右逆の移送。
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
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n}
  {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B} {j : ℕ}
  (d : PostnikovSuccessorClassInverseData R hn f j)

def PostnikovSuccessorClassInverseData.nativeRightInverseRoof :
    NativeRightInverseRoof R (f.map (postnikovFunctor R (n + 1))) j d.layerInverse.zero.stage
      (d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)) :=
  ⟨d.nonpositiveFixedRightRoof R, d.nonpositiveFixedRightRoofPath R⟩

lemma exists_postnikovSuccessorNativeRightInverseRoof (hn : 0 ≤ n) (f : LevelHom A B)
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1))))
    (lower : ∀ i, ∃ m, ∃ hi : i ≤ m,
      Nonempty (NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi))
    (i : ℕ) : ∃ m, ∃ hi : i ≤ m,
      Nonempty (NativeRightInverseRoof R (f.map (postnikovFunctor R (n + 1))) i m hi) := by
  obtain ⟨d, _⟩ := exists_postnikovSuccessorClassInverseData_after R hn f h₀ hₙ lower i i
  exact ⟨_, _, ⟨d.nativeRightInverseRoof R⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
