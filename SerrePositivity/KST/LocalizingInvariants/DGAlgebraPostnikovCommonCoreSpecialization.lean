module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreLayerInverse
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassEndpoints

/-!
概要：既存の一切断共通逆を、同じ全データを持つ共通核の入力へ送る。
方針：逆・段・細分・係数と両三角形を選び直さず移す。
規約：既存の宣言名・型は不変。使われ方：Common 系の n=1 特殊化と公開界面の保持。
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
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

namespace PostnikovCommonZeroInverse

def toCore (d : PostnikovCommonZeroInverse R 1 f c) :
    PostnikovCommonCore.ZeroInverse R (by omega) f c where
  inverseStage := d.inverseStage
  inverse_le := d.inverse_le
  inverse := d.inverse
  stage := d.stage
  source_le := d.source_le
  stage_le := d.stage_le
  base_eq := d.base_eq
  coefficient := d.coefficient
  coefficient_hom := d.coefficient_hom
  left_coefficient := d.left_coefficient
  right_coefficient := d.right_coefficient

end PostnikovCommonZeroInverse

namespace PostnikovCommonLayerInverse

def toCore (d : PostnikovCommonLayerInverse R f c) :
    PostnikovCommonCore.LayerInverse R (by omega) f c where
  zero := d.zero.toCore R f c
  coefficient := d.coefficient
  coefficient_hom := d.coefficient_hom
  left_coefficient := d.left_coefficient
  right_coefficient := d.right_coefficient

lemma toCore_coefficient (d : PostnikovCommonLayerInverse R f c) :
    (d.toCore R f c).coefficient = d.coefficient := rfl

lemma toCore_source_le (d : PostnikovCommonLayerInverse R f c) :
    (d.toCore R f c).zero.source_le = d.zero.source_le := rfl

lemma toCore_classSource (d : PostnikovCommonLayerInverse R f c) :
    PostnikovCommonCore.classSource R (by omega) f
      (postnikovOneRoofRefine R f c (d.toCore R f c).zero.source_le)
      (d.toCore R f c).coefficient = postnikovCommonClassSource R f c d := rfl

lemma toCore_classTarget (d : PostnikovCommonLayerInverse R f c) :
    PostnikovCommonCore.classTarget R (by omega) f
      (postnikovOneRoofRefine R f c (d.toCore R f c).zero.source_le) =
        postnikovCommonClassTarget R f c d := rfl

end PostnikovCommonLayerInverse
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
