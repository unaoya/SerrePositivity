module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayer
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftRestrictedMap

/-!
概要：元の共通底上の実係数逆を、class の整数 shift 係数へ移す。
方針：元の分母・分子による制限を固定し、shift の合成則で両三角形を移す。
規約：class 整合の経路は未主張。使われ方：拡大代数の逆の持ち上げ。
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

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

variable (d : PostnikovCommonLayerInverse R hn f c) (s : ℤ)

def postnikovCommonShiftedCoefficientMap :
    roofShiftedDenominatorLayer R hn f (roofRefine R hn f c d.zero.source_le) s ⟶
      roofShiftedNumeratorLayer R hn f
        (roofRefine R hn f c d.zero.source_le) s :=
  DGBimoduleShift.restrictedMap _ _ _ _ s d.coefficient

lemma postnikovCommonShiftedCoefficientMap_hom :
    (postnikovCommonShiftedCoefficientMap R hn f c d s).hom = d.coefficient.hom⟦s⟧' :=
  DGBimoduleShift.restrictedMap_hom _ _ _ _ s d.coefficient

lemma postnikovCommonShiftedCoefficientMap_left :
    (postnikovLayerMap R (f.app d.zero.stage).hom n)⟦s⟧' ≫
      (postnikovCommonShiftedCoefficientMap R hn f c d s).hom =
    (postnikovLayerMap R (A.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom n)⟦s⟧' := by
  rw [postnikovCommonShiftedCoefficientMap_hom, ← Functor.map_comp]
  exact congrArg (fun t => t⟦s⟧') d.left_coefficient

lemma postnikovCommonShiftedCoefficientMap_right :
    (postnikovCommonShiftedCoefficientMap R hn f c d s).hom ≫
      (postnikovLayerMap R (f.app i).hom n)⟦s⟧' =
    (postnikovLayerMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom n)⟦s⟧' := by
  rw [postnikovCommonShiftedCoefficientMap_hom, ← Functor.map_comp]
  exact congrArg (fun t => t⟦s⟧') d.right_coefficient

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
