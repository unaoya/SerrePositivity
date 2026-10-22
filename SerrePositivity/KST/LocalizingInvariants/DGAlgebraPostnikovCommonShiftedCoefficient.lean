module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonLayerInverse
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

def postnikovOneRoofShiftedDenominatorLayer (s : ℤ) : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.denominator (postnikovShiftedLayerBimodule R (B.obj m).obj 1 (by omega) s)

def postnikovOneRoofShiftedNumeratorLayer (s : ℤ) : Bimod c.roof.apex c.roof.apex :=
  bimoduleRestrict c.roof.numerator (postnikovShiftedLayerBimodule R (A.obj i).obj 1 (by omega) s)

variable (d : PostnikovCommonLayerInverse R f c) (s : ℤ)

def postnikovCommonShiftedCoefficientMap :
    postnikovOneRoofShiftedDenominatorLayer R f (postnikovOneRoofRefine R f c d.zero.source_le) s ⟶
      postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) s :=
  DGBimoduleShift.restrictedMap _ _ _ _ s d.coefficient

lemma postnikovCommonShiftedCoefficientMap_hom :
    (postnikovCommonShiftedCoefficientMap R f c d s).hom = d.coefficient.hom⟦s⟧' :=
  DGBimoduleShift.restrictedMap_hom _ _ _ _ s d.coefficient

lemma postnikovCommonShiftedCoefficientMap_left :
    (postnikovLayerMap R (f.app d.zero.stage).hom 1)⟦s⟧' ≫
      (postnikovCommonShiftedCoefficientMap R f c d s).hom =
    (postnikovLayerMap R (A.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1)⟦s⟧' := by
  rw [postnikovCommonShiftedCoefficientMap_hom, ← Functor.map_comp]
  exact congrArg (fun t => t⟦s⟧') d.left_coefficient

lemma postnikovCommonShiftedCoefficientMap_right :
    (postnikovCommonShiftedCoefficientMap R f c d s).hom ≫
      (postnikovLayerMap R (f.app i).hom 1)⟦s⟧' =
    (postnikovLayerMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1)⟦s⟧' := by
  rw [postnikovCommonShiftedCoefficientMap_hom, ← Functor.map_comp]
  exact congrArg (fun t => t⟦s⟧') d.right_coefficient

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
