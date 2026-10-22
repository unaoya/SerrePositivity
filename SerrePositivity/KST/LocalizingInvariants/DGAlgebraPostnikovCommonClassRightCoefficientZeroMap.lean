module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRightCoefficientTriangle
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

/-!
概要：実 fⱼ 係数射の零 class 像が、元の native class 互換性で使った右射と一致する。
方針：元の P 底射と層射を保つ二座標の公式を比較する。
規約：実代数射全体の等式を保持。使われ方：fixed 模型射の係数表示と native 経路の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonClassRightTargetCoefficient_zero_map :
    SquareZero.coefficientMap (postnikovCommonClassBase R f c d)
      (postnikovCommonClassRightTargetCoefficient R f c d hj) ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    postnikovCommonClassFixedZeroMap R f c d hj := by
  apply Mon.Hom.ext
  rw [Mon.comp_hom', SquareZero.coefficientMap_hom,
    postnikovCommonClassRightTargetCoefficient_hom, SquareZero.baseChangeMap_hom,
    postnikovCommonClassFixedZeroMap, Mon.comp_hom',
    postnikovCommonClassTransitionToZero_hom, postnikovZeroClassMap_hom,
    cochainBiprodMap_comp, cochainBiprodMap_comp]
  simp only [Category.id_comp, ← Mon.comp_hom']
  let hb := (Category.assoc (postnikovCommonClassRetractBase R f c d (hj := hj))
    (postnikovTransition R (A.obj j).obj 1 0 (by omega)) (postnikovMap R (f.app j).hom 0)).trans
    (postnikovCommonClassFixedZeroBase_classifying R f c d hj)
  exact congrArg (fun b => biprod.map b.hom
    ((postnikovLayerMap R (f.app j).hom 1)⟦(1 : ℤ)⟧')) hb.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
