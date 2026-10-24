module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonZeroInverse
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCoefficientFromZero
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofCoefficientBimodules

/-!
概要：共通零底上で構成した係数逆を、元の細分 roof の実層双加群射へ戻す。
方針：同じ層の恒等 underlying 制限同型と、元の商射に沿う実制限射を合成する。
規約：左右作用と元の cochain 三角形を保持。使われ方：class 整合と実代数逆の持ち上げ。
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
  (d : PostnikovCommonZeroInverse R 1 f c)

@[reducible]
def postnikovCommonCoefficientMap :
    postnikovOneRoofDenominatorLayer R f (postnikovOneRoofRefine R f c d.source_le) ⟶
      postnikovOneRoofNumeratorLayer R f (postnikovOneRoofRefine R f c d.source_le) :=
  postnikovCoefficientFromZero R f (postnikovOneRoofRefine R f c d.source_le) d.coefficient

lemma postnikovCommonCoefficientMap_zero_hom :
    (postnikovCommonCoefficientMap R f c d).hom = d.coefficient.hom :=
  postnikovCoefficientFromZero_hom R f (postnikovOneRoofRefine R f c d.source_le) d.coefficient

lemma postnikovCommonCoefficientMap_hom : (postnikovCommonCoefficientMap R f c d).hom =
    postnikovLayerMap R (B.transition d.stage_le).hom 1 ≫ d.inverse.coefficient.hom :=
  (postnikovCommonCoefficientMap_zero_hom R f c d).trans d.coefficient_hom

lemma postnikovCommonCoefficientMap_left : postnikovLayerMap R (f.app d.stage).hom 1 ≫
    (postnikovCommonCoefficientMap R f c d).hom =
      postnikovLayerMap R (A.transition (d.inverse_le.trans d.stage_le)).hom 1 :=
  (congrArg (fun t => postnikovLayerMap R (f.app d.stage).hom 1 ≫ t)
    (postnikovCommonCoefficientMap_zero_hom R f c d)).trans d.left_coefficient

lemma postnikovCommonCoefficientMap_right : (postnikovCommonCoefficientMap R f c d).hom ≫
    postnikovLayerMap R (f.app i).hom 1 =
      postnikovLayerMap R (B.transition (d.inverse_le.trans d.stage_le)).hom 1 :=
  (congrArg (fun t => t ≫ postnikovLayerMap R (f.app i).hom 1)
    (postnikovCommonCoefficientMap_zero_hom R f c d)).trans d.right_coefficient

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
