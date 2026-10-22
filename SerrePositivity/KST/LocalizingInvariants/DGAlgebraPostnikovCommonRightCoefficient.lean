module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonLayerInverse
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonZeroRightCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerZeroRestrictionIso
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionOver

/-!
概要：零底上の右係数標的と二つの実射を、元の細分 roof 底へ戻す。
方針：元の商射による制限と恒等 underlying 比較を使い、元の係数三角形で照合する。
規約：同じ逆・細分・元の f と遷移を保持。使われ方：class 標的上の右三角形。
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

local instance commonRight_apex_nonpositive :
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex.X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive

def postnikovCommonRightLayer :
    Bimod (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex :=
  bimoduleRestrict
    (postnikovQuotient R (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex 0)
    (postnikovCommonZeroRightLayer R 1 f c d.zero)

def postnikovCommonRightNumeratorMap :
    postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c d.zero.source_le) ⟶
      postnikovCommonRightLayer R f c d :=
  (postnikovLayerBaseZeroRestrictionIso R (A.obj i).obj _ 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator).hom ≫
      bimoduleRestrictionMap
        (postnikovQuotient R (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex 0)
        (postnikovCommonZeroRightNumeratorMap R 1 f c d.zero)

lemma postnikovCommonRightNumeratorMap_hom :
    (postnikovCommonRightNumeratorMap R f c d).hom = postnikovLayerMap R (f.app i).hom 1 := by
  unfold postnikovCommonRightNumeratorMap
  rw [Bimod.comp_hom', postnikovLayerBaseZeroRestrictionIso_hom, bimoduleRestrictionMap_hom,
    postnikovCommonZeroRightNumeratorMap_hom]
  exact Category.id_comp _

def postnikovCommonRightDenominatorMap :
    postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c d.zero.source_le) ⟶
      postnikovCommonRightLayer R f c d :=
  (postnikovLayerBaseZeroRestrictionIso R (B.obj d.zero.stage).obj _ 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator).hom ≫
      bimoduleRestrictionMap
        (postnikovQuotient R (postnikovOneRoofRefine R f c d.zero.source_le).roof.apex 0)
        (postnikovCommonZeroRightDenominatorMap R 1 f c d.zero)

lemma postnikovCommonRightDenominatorMap_hom :
    (postnikovCommonRightDenominatorMap R f c d).hom =
      postnikovLayerMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1 := by
  unfold postnikovCommonRightDenominatorMap
  rw [Bimod.comp_hom', postnikovLayerBaseZeroRestrictionIso_hom, bimoduleRestrictionMap_hom,
    postnikovCommonZeroRightDenominatorMap_hom]
  exact Category.id_comp _

lemma postnikovCommonRight_coefficient : d.coefficient ≫
    postnikovCommonRightNumeratorMap R f c d = postnikovCommonRightDenominatorMap R f c d := by
  apply Bimod.Hom.ext
  exact (Bimod.comp_hom' _ _).trans
    ((congrArg (fun t => d.coefficient.hom ≫ t)
      (postnikovCommonRightNumeratorMap_hom R f c d)).trans
        (d.right_coefficient.trans (postnikovCommonRightDenominatorMap_hom R f c d).symm))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
