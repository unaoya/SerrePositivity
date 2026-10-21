module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBaseNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerRestrictionIso
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftRestriction
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProjection

/-!
概要：Postnikov 層の整数 shift を、元の底の切断代数上の実 dg 双加群として供給する。
方針：検証済みの shift 関手と制限比較を、元の層双加群・比較射に適用する。
規約：導来拡大の分類は未主張。使われ方：Postnikov derivation の係数と標的。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (s : ℤ)

def postnikovShiftedLayerBimodule : Bimod (postnikov R B n) (postnikov R B n) :=
  DGBimoduleShift.obj (postnikovLayerBaseBimodule R B n hn) s

lemma postnikovShiftedLayer_upperBound :
    (postnikovShiftedLayerBimodule R B n hn s).X.IsStrictlyLE (-(n + 1) - s) := by
  have : (postnikovLayerBaseBimodule R B n hn).X.IsStrictlyLE (-(n + 1)) :=
    postnikovLayer_upperBound R B n
  exact DGBimoduleShift.obj_upperBound _ s (-(n + 1))

lemma postnikovShiftedLayer_lowerBound :
    (postnikovShiftedLayerBimodule R B n hn s).X.IsStrictlyGE (-(n + 1) - s) := by
  have : (postnikovLayerBaseBimodule R B n hn).X.IsStrictlyGE (-(n + 1)) :=
    postnikovLayer_lowerBound R B n
  exact DGBimoduleShift.obj_lowerBound _ s (-(n + 1))

def postnikovShiftedLayerMap {C : Mon (Complex R)} [C.X.IsStrictlyLE 0] (f : B ⟶ C) :
    postnikovShiftedLayerBimodule R B n hn s ⟶
      bimoduleRestrict (postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn s) :=
  DGBimoduleShift.mapOver (postnikovMap R f n) (postnikovLayerBaseBimodule R C n hn) s
    (postnikovLayerBaseMap R f n hn)

lemma postnikovShiftedLayerMap_hom {C : Mon (Complex R)} [C.X.IsStrictlyLE 0] (f : B ⟶ C) :
    (postnikovShiftedLayerMap R B n hn s f).hom = (postnikovLayerMap R f n)⟦s⟧' :=
  DGBimoduleShift.mapOver_hom _ _ _ _

def postnikovShiftedLayerRestrictionIso :
    DGBimoduleShift.obj (postnikovLayerBimodule R B n) s ≅
      bimoduleRestrict (postnikovTransition R B (n + 1) n (by omega))
        (postnikovShiftedLayerBimodule R B n hn s) :=
  (DGBimoduleShift.functor (postnikov R B (n + 1)) s).mapIso
    (postnikovLayerBaseRestrictionIso R B n hn) ≪≫
      DGBimoduleShift.restrictionIso _ (postnikovLayerBaseBimodule R B n hn) s

def postnikovDerivationTarget : Mon (Complex R) :=
  SquareZero.algebra (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
