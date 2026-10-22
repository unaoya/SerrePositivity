module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroDescNaturality
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionBaseEquality

/-!
概要：共通底の右係数標的を、元の分子と f の合成に沿う標準の層制限と同定する。
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

local instance commonRightBase_apex_nonpositive :
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex.X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive
local instance commonRightBase_target_lowerBound :
    (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightBase : (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex ⟶
    postnikov R (B.obj i).obj 1 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫ postnikovMap R (f.app i).hom 1

lemma postnikovCommonRightBase_zero :
    postnikovDesc R 0 (postnikovCommonRightBase R f c d ≫
      postnikovTransition R (B.obj i).obj 1 0 (by omega)) =
    postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c d.zero.source_le) ≫
      postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 0 :=
  (postnikovZeroDesc_map R (A.obj i).obj (B.obj i).obj _ 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).trans
      (postnikovCommonZeroInverse_right_base R 1 f c d.zero)

def postnikovCommonRightBaseIso :
    bimoduleRestrict (postnikovCommonRightBase R f c d)
      (postnikovLayerBaseBimodule R (B.obj i).obj 1 (by omega)) ≅
        postnikovCommonRightLayer R f c d :=
  postnikovLayerBaseZeroRestrictionIso R (B.obj i).obj _ 1 (by omega)
    (postnikovCommonRightBase R f c d) ≪≫
      bimoduleRestrictionBaseEqIso
        (postnikovQuotient R (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex 0)
        (postnikovCommonRightBase_zero R f c d) (postnikovLayerZeroBimodule R (B.obj i).obj 1)

lemma postnikovCommonRightBaseIso_hom : (postnikovCommonRightBaseIso R f c d).hom.hom =
    𝟙 (postnikovLayer R (B.obj i).obj 1) := by
  unfold postnikovCommonRightBaseIso
  change (postnikovLayerBaseZeroRestrictionIso R (B.obj i).obj _ 1 (by omega)
    (postnikovCommonRightBase R f c d)).hom.hom ≫
    (bimoduleRestrictionBaseEqIso _ (postnikovCommonRightBase_zero R f c d)
      (postnikovLayerZeroBimodule R (B.obj i).obj 1)).hom.hom = _
  rw [postnikovLayerBaseZeroRestrictionIso_hom, bimoduleRestrictionBaseEqIso_hom]
  exact Category.id_comp _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
