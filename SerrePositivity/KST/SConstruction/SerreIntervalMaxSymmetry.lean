module
public import SerrePositivity.KST.SConstruction.SerreIntervalTensorExt
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxValues

/-! # 元の max connection の signed 対称性
概要：元の max connection が Koszul braiding に沿って対称であることを証明する。
方針：全斉次生成元の対で判定し、二つの辺では零性により交差符号を保持する。
規約：元の辺と braiding を変更しない。使われ方：connection の Serre 対角保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の max connection は、元の Koszul braiding に沿って対称。 -/
lemma serreIntervalMax_symmetric :
    (signedSwap (serreInterval A) (serreInterval A)).hom ≫ serreIntervalMax A =
      serreIntervalMax A := by
  apply serreIntervalTensor_hom_ext A
  intro i j n hn
  simp only [chain_comp_apply]
  fin_cases i <;> fin_cases j
  all_goals
    first
    | have hn' : n = 0 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -1 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -2 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    rcases hn' with rfl
    dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
    rw [signedSwap_apply]
    simp only [zero_mul, mul_zero, Int.negOnePow_zero, one_smul,
      Units.smul_def, map_zsmul, serreIntervalMax_zero_apply, serreIntervalMax_one_apply,
      serreIntervalMax_edge_zero, serreIntervalMax_edge_one, serreIntervalMax_edge_edge,
      chain_comp_apply, serreIntervalAugmentation_zero_value,
      serreIntervalAugmentation_one_value, serreIntervalAugmentation_edge, map_zero, smul_zero]
  all_goals rfl

end SerrePositivity.KST.SConstruction
