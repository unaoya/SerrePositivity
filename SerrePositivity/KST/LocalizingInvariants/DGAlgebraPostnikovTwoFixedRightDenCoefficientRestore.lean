module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDenRestore

/-!
概要：元の直接分母係数模型射を、元の B 遷移の class 標的射へ戻す。
方針：元の双加群射の全射式と係数同型の恒等 underlying 射を使う。
規約：H⁻² だけでなく実係数射の三角形。使われ方：直接模型射の元の分母比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma rightDenominatorCoefficientIso_hom : (d.rightDenominatorCoefficientIso R).hom.hom =
    𝟙 ((postnikovLayer R (B.obj j).obj 1)⟦(1 : ℤ)⟧) := by
  simp only [rightDenominatorCoefficientIso, Iso.trans_hom, Bimod.comp_hom',
    bimoduleRestrictBaseEqIso_hom]
  change 𝟙 ((postnikovLayer R (B.obj j).obj 1)⟦(1 : ℤ)⟧) ≫ (𝟙 _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.id_comp]

lemma rightDenominatorCoefficient_factor : d.rightDenominatorCoefficient R =
    postnikovCellClassOverCoefficient R (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj
      (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
      (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le) ≫
        (d.rightDenominatorCoefficientIso R).hom := by
  apply Bimod.Hom.ext
  rw [rightDenominatorCoefficient, postnikovCommonClassRightDenominatorCoefficient_hom,
    Bimod.comp_hom', postnikovCellClassOverCoefficient_hom, d.rightDenominatorCoefficientIso_hom R]
  change (postnikovLayerMap R
    (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le) 1)⟦(1 : ℤ)⟧' =
    (postnikovLayerMap R
      (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le) 1)⟦(1 : ℤ)⟧' ≫
        𝟙 ((postnikovLayer R (B.obj j).obj 1)⟦(1 : ℤ)⟧)
  exact (Category.comp_id _).symm

lemma rightDenominatorCoefficient_restore :
    SquareZero.coefficientMap (d.classBase R) (d.rightDenominatorCoefficient R) ≫
      d.rightDenominatorClassRestore R =
    SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
      (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1) ≫
      postnikovDerivationTargetMap R
        (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
        1 (by omega) := by
  rw [d.rightDenominatorCoefficient_factor R]
  let h := SquareZero.coefficientRestore_coefficient
    (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le)
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
    (d.rightDenominatorCoefficientIso R)
    (postnikovCellClassOverCoefficient R (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj
      (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
      (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le))
  exact h.trans (SquareZero.restrictionCoefficient_baseChange _ _ _ _ _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
