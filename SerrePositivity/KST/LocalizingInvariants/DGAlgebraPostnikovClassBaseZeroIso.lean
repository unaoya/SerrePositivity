module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

/-!
概要：任意の共通底で、元の class 標的と零 class 標的の底変更を実同型で比較する。
方針：零切断への恒等係数射の作用保存から双加群同型を作り、平方零関手で移す。
規約：元の底射・係数・零標的への射を保持。使われ方：遷移後の class 経路の端点同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B P : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (s : ℤ) (b : P ⟶ postnikov R B n)

def postnikovClassBaseZeroCoefficient :
    bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn s) ⟶
      bimoduleRestrict (b ≫ postnikovTransition R B n 0 hn)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s) :=
  bimoduleRestrictOver b (b ≫ postnikovTransition R B n 0 hn)
    (postnikovTransition R B n 0 hn) rfl (postnikovShiftedLayerToZeroBase R B n hn s)

lemma postnikovClassBaseZeroCoefficient_hom :
    (postnikovClassBaseZeroCoefficient R B P n hn s b).hom =
      𝟙 ((postnikovLayer R B n)⟦s⟧) := by
  rw [postnikovClassBaseZeroCoefficient, bimoduleRestrictOver_hom,
    postnikovShiftedLayerToZeroBase_hom]

def postnikovClassBaseZeroCoefficientIso :
    bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn s) ≅
      bimoduleRestrict (b ≫ postnikovTransition R B n 0 hn)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s) := by
  refine Bimod.isoOfIso (Iso.refl ((postnikovLayer R B n)⟦s⟧)) ?_ ?_
  · have h := (postnikovClassBaseZeroCoefficient R B P n hn s b).left_act_hom
    rw [postnikovClassBaseZeroCoefficient_hom] at h
    exact h
  · have h := (postnikovClassBaseZeroCoefficient R B P n hn s b).right_act_hom
    rw [postnikovClassBaseZeroCoefficient_hom] at h
    exact h

def postnikovClassBaseZeroIso :
    SquareZero.algebra P (bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn s)) ≅
      SquareZero.algebra P (bimoduleRestrict (b ≫ postnikovTransition R B n 0 hn)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)) :=
  SquareZero.coefficientIso P (postnikovClassBaseZeroCoefficientIso R B P n hn s b)

lemma postnikovClassBaseZeroIso_projection : (postnikovClassBaseZeroIso R B P n hn s b).hom ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.coefficientMap_projection _ _

lemma postnikovClassBaseZeroIso_inv_projection : (postnikovClassBaseZeroIso R B P n hn s b).inv ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.coefficientMap_projection _ _

lemma postnikovClassBaseZeroIso_map : (postnikovClassBaseZeroIso R B P n hn s b).hom ≫
    SquareZero.baseChangeMap (b ≫ postnikovTransition R B n 0 hn)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s) =
        SquareZero.baseChangeMap b (postnikovShiftedLayerBimodule R B n hn s) ≫
          postnikovClassToZeroBase R B n hn s := by
  apply Mon.Hom.ext
  change biprod.map (𝟙 P.X) (𝟙 ((postnikovLayer R B n)⟦s⟧)) ≫
    (SquareZero.baseChangeMap (b ≫ postnikovTransition R B n 0 hn)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)).hom =
        (SquareZero.baseChangeMap b (postnikovShiftedLayerBimodule R B n hn s)).hom ≫
          (postnikovClassToZeroBase R B n hn s).hom
  rw [SquareZero.baseChangeMap_hom, SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom]
  change biprod.map (𝟙 P.X) (𝟙 ((postnikovLayer R B n)⟦s⟧)) ≫
    biprod.map (b.hom ≫ (postnikovTransition R B n 0 hn).hom) (𝟙 _) =
      biprod.map b.hom (𝟙 ((postnikovLayer R B n)⟦s⟧)) ≫
        biprod.map (postnikovTransition R B n 0 hn).hom (𝟙 ((postnikovLayer R B n)⟦s⟧))
  apply biprod.hom_ext <;> simp [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
