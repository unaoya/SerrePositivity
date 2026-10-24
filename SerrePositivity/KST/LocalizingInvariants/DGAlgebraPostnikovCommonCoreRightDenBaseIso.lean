module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroDescNaturality
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionBaseEquality

/-!
概要：共通底の右係数標的を、元の分母と B の遷移の合成に沿う標準の層制限と同定する。
方針：零降下の自然性と元の右底三角形で二重制限の底射を厳密に一致させる。
規約：underlying は元の B の層の恒等。使われ方：元の class 自然性との接続。
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
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

local instance commonRightDenBase_apex_nonpositive :
    (roofRefine R hn f c d.zero.source_le).roof.apex.X.IsStrictlyLE 0 :=
  (roofRefine R hn f c d.zero.source_le).roof_nonpositive
local instance commonRightDenBase_target_lowerBound :
    (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightDenBase : (roofRefine R hn f c d.zero.source_le).roof.apex ⟶
    postnikov R (B.obj i).obj n :=
  (roofRefine R hn f c d.zero.source_le).roof.denominator ≫
    postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom n

lemma postnikovCommonRightDenBase_zero :
    postnikovDesc R 0 (postnikovCommonRightDenBase R hn f c d ≫
      postnikovTransition R (B.obj i).obj n 0 (by omega)) =
    roofZeroDenominator R hn f (roofRefine R hn f c d.zero.source_le) ≫
      postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 0 :=
  postnikovZeroDesc_map R (B.obj d.zero.stage).obj (B.obj i).obj _ n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom

def postnikovCommonRightDenBaseIso :
    bimoduleRestrict (postnikovCommonRightDenBase R hn f c d)
      (postnikovLayerBaseBimodule R (B.obj i).obj n hn) ≅
        postnikovCommonRightLayer R hn f c d :=
  postnikovLayerBaseZeroRestrictionIso R (B.obj i).obj _ n hn
    (postnikovCommonRightDenBase R hn f c d) ≪≫
      bimoduleRestrictionBaseEqIso
        (postnikovQuotient R (roofRefine R hn f c d.zero.source_le).roof.apex 0)
        (postnikovCommonRightDenBase_zero R hn f c d) (postnikovLayerZeroBimodule R (B.obj i).obj n)

lemma postnikovCommonRightDenBaseIso_hom : (postnikovCommonRightDenBaseIso R hn f c d).hom.hom =
    𝟙 (postnikovLayer R (B.obj i).obj n) := by
  unfold postnikovCommonRightDenBaseIso
  change (postnikovLayerBaseZeroRestrictionIso R (B.obj i).obj _ n hn
    (postnikovCommonRightDenBase R hn f c d)).hom.hom ≫
    (bimoduleRestrictionBaseEqIso _ (postnikovCommonRightDenBase_zero R hn f c d)
      (postnikovLayerZeroBimodule R (B.obj i).obj n)).hom.hom = _
  rw [postnikovLayerBaseZeroRestrictionIso_hom, bimoduleRestrictionBaseEqIso_hom]
  exact Category.id_comp _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
