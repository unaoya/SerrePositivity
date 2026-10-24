module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreFromZero
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreInput

/-!
概要：共通核の任意次数の入力を、零底係数と両三角形を持つ実データへ展開する。
方針：選んだ共通零底と同じ細分・層逆を使い、同じ underlying 射を保持する。
規約：底の一致や作用保存を追加仮定にしない。使われ方：元の共通底上の係数逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

structure ZeroInverse where
  inverseStage : ℕ
  inverse_le : i ≤ inverseStage
  inverse : PostnikovZeroLayerInverse R n f i inverseStage inverse_le
  stage : ℕ
  source_le : m ≤ stage
  stage_le : inverseStage ≤ stage
  base_eq : PostnikovRoofZeroSpan.numerator R n hn f (c.refine R source_le) =
    PostnikovRoofZeroSpan.denominator R n hn f (c.refine R source_le) ≫
      postnikovMap R (B.transition stage_le).hom 0 ≫ inverse.base
  coefficient : zeroDenominatorLayer R hn f
      (c.refine R source_le) ⟶
    zeroNumeratorLayer R hn f (c.refine R source_le)
  coefficient_hom : coefficient.hom =
    postnikovLayerMap R (B.transition stage_le).hom n ≫ inverse.coefficient.hom
  left_coefficient : postnikovLayerMap R (f.app stage).hom n ≫ coefficient.hom =
    postnikovLayerMap R (A.transition (inverse_le.trans stage_le)).hom n
  right_coefficient : coefficient.hom ≫ postnikovLayerMap R (f.app i).hom n =
    postnikovLayerMap R (B.transition (inverse_le.trans stage_le)).hom n

namespace ZeroInverse

def ofInput (d : Input R hn f c) : ZeroInverse R hn f c where
  inverseStage := d.inverseStage
  inverse_le := d.target_le
  inverse := d.inverse
  stage := d.stage
  source_le := d.source_le
  stage_le := d.inverse_le
  base_eq := d.base_eq
  coefficient := PostnikovRoofZeroSpan.zeroCoefficient R n hn f c d.inverse
    d.source_le d.inverse_le d.base_eq
  coefficient_hom := PostnikovRoofZeroSpan.zeroCoefficient_hom R n hn f c d.inverse
    d.source_le d.inverse_le d.base_eq
  left_coefficient := PostnikovRoofZeroSpan.zeroCoefficient_left R n hn f c d.inverse
    d.source_le d.inverse_le d.base_eq
  right_coefficient := PostnikovRoofZeroSpan.zeroCoefficient_right R n hn f c d.inverse
    d.source_le d.inverse_le d.base_eq

end ZeroInverse
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
