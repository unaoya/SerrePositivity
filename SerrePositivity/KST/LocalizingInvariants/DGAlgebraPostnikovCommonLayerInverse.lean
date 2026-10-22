module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoefficient

/-!
概要：元の π₀・π₂ 群の pro 同型から、元の細分 roof 上の実係数双加群逆を供給する。
方針：共通零底の実逆を、同じ係数・作用比較を保って元の底上へ移す。
規約：class 整合・拡大代数の逆は未主張。使われ方：Postnikov 拡大の逆の持ち上げ。
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
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

structure PostnikovCommonLayerInverse where
  zero : PostnikovCommonZeroInverse R 1 f c
  coefficient : postnikovOneRoofDenominatorLayer R f
      (postnikovOneRoofRefine R f c zero.source_le) ⟶
    postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c zero.source_le)
  coefficient_hom : coefficient.hom = zero.coefficient.hom
  left_coefficient : postnikovLayerMap R (f.app zero.stage).hom 1 ≫ coefficient.hom =
    postnikovLayerMap R (A.transition (zero.inverse_le.trans zero.stage_le)).hom 1
  right_coefficient : coefficient.hom ≫ postnikovLayerMap R (f.app i).hom 1 =
    postnikovLayerMap R (B.transition (zero.inverse_le.trans zero.stage_le)).hom 1

namespace PostnikovCommonLayerInverse

def ofZeroInverse (d : PostnikovCommonZeroInverse R 1 f c) :
    PostnikovCommonLayerInverse R f c where
  zero := d
  coefficient := postnikovCommonCoefficientMap R f c d
  coefficient_hom := postnikovCommonCoefficientMap_zero_hom R f c d
  left_coefficient := postnikovCommonCoefficientMap_left R f c d
  right_coefficient := postnikovCommonCoefficientMap_right R f c d

end PostnikovCommonLayerInverse

def postnikovCommonLayerInverse
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2))) :
    PostnikovCommonLayerInverse R f c :=
  PostnikovCommonLayerInverse.ofZeroInverse R f c
    (postnikovCommonZeroInverse R 1 f c (by omega) h₀ h₂)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
