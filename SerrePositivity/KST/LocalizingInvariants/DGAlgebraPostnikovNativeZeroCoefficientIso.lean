module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso

/-!
概要：元の Postnikov class 係数を、零切断に沿う制限係数と実同型で比較する。
方針：既存の恒等 underlying 射の両作用保存から双加群同型を構成する。
規約：元の class 標的・射影・零底射を保持。使われ方：動く底の模型経路の適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (s : ℤ)

def postnikovNativeZeroCoefficientIso : postnikovShiftedLayerBimodule R B n hn s ≅
    bimoduleRestrict (postnikovTransition R B n 0 hn)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s) := by
  refine Bimod.isoOfIso (Iso.refl ((postnikovLayer R B n)⟦s⟧)) ?_ ?_
  · have h := (postnikovShiftedLayerToZeroBase R B n hn s).left_act_hom
    rw [postnikovShiftedLayerToZeroBase_hom] at h
    exact h
  · have h := (postnikovShiftedLayerToZeroBase R B n hn s).right_act_hom
    rw [postnikovShiftedLayerToZeroBase_hom] at h
    exact h

def postnikovNativeZeroIso :
    SquareZero.algebra (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn s) ≅
      SquareZero.algebra (postnikov R B n)
        (bimoduleRestrict (postnikovTransition R B n 0 hn)
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)) :=
  SquareZero.coefficientIso _ (postnikovNativeZeroCoefficientIso R B n hn s)

lemma postnikovNativeZeroIso_projection : (postnikovNativeZeroIso R B n hn s).hom ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ :=
  SquareZero.coefficientMap_projection _ _

lemma postnikovNativeZeroIso_map : (postnikovNativeZeroIso R B n hn s).hom ≫
    SquareZero.baseChangeMap (postnikovTransition R B n 0 hn)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s) =
        postnikovClassToZeroBase R B n hn s := by
  apply Mon.Hom.ext
  change (postnikovNativeZeroIso R B n hn s).hom.hom ≫
    (SquareZero.baseChangeMap (postnikovTransition R B n 0 hn)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)).hom = _
  rw [SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom]
  change biprod.map (𝟙 _) (𝟙 _) ≫ biprod.map _ (𝟙 _) = biprod.map _ (𝟙 _)
  apply biprod.hom_ext <;> simp [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
