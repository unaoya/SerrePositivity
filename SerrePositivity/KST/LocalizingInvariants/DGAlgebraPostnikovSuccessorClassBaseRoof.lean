module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassInverseData
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInverseRoofRetarget

/-!
概要：次段切断 class 整合データの共通底を、同じ低い対象段の実 τₙ 逆 roof として回収する。
方針：選択した元の roof を同じ後続段へ細分し、元の A の遷移で対象段を移す。
規約：class 経路の底と厳密に同じ分子・分母。使われ方：実次段切断逆への持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def lowerBaseInverse : NonpositiveInverseRoof R (f.map (postnikovFunctor R n))
    j d.layerInverse.zero.stage
      (d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)) :=
  (PostnikovCommonCore.roofRefine R hn f d.baseInverse d.layerInverse.zero.source_le).retarget R d.target_le

lemma lowerBaseInverse_numerator : (d.lowerBaseInverse R).roof.numerator =
    PostnikovCommonCore.postnikovCommonClassRetractBase R hn f d.baseInverse d.layerInverse (hj := d.target_le) := rfl

lemma lowerBaseInverse_denominator : (d.lowerBaseInverse R).roof.denominator =
    (PostnikovCommonCore.roofRefine R hn f d.baseInverse d.layerInverse.zero.source_le).roof.denominator := rfl

lemma lowerBaseInverse_apex : (d.lowerBaseInverse R).roof.apex =
    PostnikovCommonCore.postnikovCommonClassBase R hn f d.baseInverse d.layerInverse := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
