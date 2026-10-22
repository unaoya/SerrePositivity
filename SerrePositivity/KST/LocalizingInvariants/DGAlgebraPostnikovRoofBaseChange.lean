module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangeConnectivity
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoof

/-!
概要：元の隣接拡大を実 roof の分母に沿って底変更し、元の上段への実比較を供給する。
方針：元の分母の次数全射準同型性を底変更し、元の係数層と新しい底への連結度を保つ。
規約：roof の分子側との比較は別工程。使われ方：元の二切断射の逆の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)
  {C : Mon (Complex R)} (r : SurjectiveRoof R (postnikov R B n) C)

def postnikovRoofBaseChange : Mon (Complex R) :=
  postnikovExtensionBaseChange R B n r.denominator

def postnikovRoofBaseChangeUpperInverse :
    SurjectiveRoof R (postnikov R B (n + 1)) (postnikovRoofBaseChange R B n r) where
  apex := postnikovRoofBaseChange R B n r
  denominator := postnikovExtensionBaseChangeUpper R B n r.denominator
  numerator := 𝟙 _
  denominator_epi := by
    have := r.denominator_epi
    exact postnikovExtensionBaseChangeUpper_epi R B n r.denominator
  denominator_quasiIso := by
    have := r.denominator_epi
    exact postnikovExtensionBaseChangeUpper_quasiIso R B n r.denominator r.denominator_quasiIso

lemma postnikovRoofBaseChange_nonpositive (hr : r.apex.X.IsStrictlyLE 0) :
    (postnikovRoofBaseChange R B n r).X.IsStrictlyLE 0 := by
  have := hr
  exact postnikovExtensionBaseChange_nonpositive R B n r.denominator

lemma postnikovRoofBaseChangeBase_connected :
    IsConnected R (postnikovExtensionBaseChangeBase R B n r.denominator) (n + 1) :=
  postnikovExtensionBaseChangeBase_connected R B n r.denominator

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
