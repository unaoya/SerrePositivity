module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxAugmentation
public import SerrePositivity.KST.SConstruction.SerreIntervalDiagonalEndpoints
public import SerrePositivity.KST.SConstruction.TensorInterchangeMapValues

/-! # 元の max connection の Serre 対角保存
概要：元の max connection は、signed 交差を持つ tensor Serre 対角を保存する。
方針：元の九つの生成元の対で判定し、端点・辺の同じ値と tensor 交差式を使う。
規約：Serre 対角の非対称な因子順を保持する。使われ方：cubical connection の余モノイド射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

private lemma max_diagonal_case_00 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (0)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 0) (serreIntervalGeneratorDegree 0) (0) (by decide)
          (serreIntervalGenerator A 0 ⊗ₜ[A] serreIntervalGenerator A 0)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (0)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 0) (serreIntervalGeneratorDegree 0) (0) (by decide)
          (serreIntervalGenerator A 0 ⊗ₜ[A] serreIntervalGenerator A 0)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_zero_apply, serreIntervalDiagonal_zero_value]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [one_smul]



private lemma max_diagonal_case_01 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (0)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 0) (serreIntervalGeneratorDegree 1) (0) (by decide)
          (serreIntervalGenerator A 0 ⊗ₜ[A] serreIntervalGenerator A 1)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (0)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 0) (serreIntervalGeneratorDegree 1) (0) (by decide)
          (serreIntervalGenerator A 0 ⊗ₜ[A] serreIntervalGenerator A 1)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_zero_apply, serreIntervalDiagonal_zero_value,
    serreIntervalDiagonal_one_value]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [one_smul]



private lemma max_diagonal_case_02 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (-1)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 0) (serreIntervalGeneratorDegree 2) (-1) (by decide)
          (serreIntervalGenerator A 0 ⊗ₜ[A] serreIntervalGenerator A 2)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (-1)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 0) (serreIntervalGeneratorDegree 2) (-1) (by decide)
          (serreIntervalGenerator A 0 ⊗ₜ[A] serreIntervalGenerator A 2)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_zero_apply, serreIntervalDiagonal_zero_value,
    serreIntervalDiagonal_edge, serreIntervalDiagonalEdge, TensorProduct.tmul_add, map_add]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [one_smul]



private lemma max_diagonal_case_10 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (0)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 1) (serreIntervalGeneratorDegree 0) (0) (by decide)
          (serreIntervalGenerator A 1 ⊗ₜ[A] serreIntervalGenerator A 0)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (0)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 1) (serreIntervalGeneratorDegree 0) (0) (by decide)
          (serreIntervalGenerator A 1 ⊗ₜ[A] serreIntervalGenerator A 0)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_one_apply, chain_comp_apply, serreIntervalAugmentation_zero_value,
    serreIntervalDiagonal_zero_value, serreIntervalDiagonal_one_value]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [serreIntervalAugmentation_zero_value, one_smul]
  exact serreIntervalDiagonal_one_value A


private lemma max_diagonal_case_11 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (0)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 1) (serreIntervalGeneratorDegree 1) (0) (by decide)
          (serreIntervalGenerator A 1 ⊗ₜ[A] serreIntervalGenerator A 1)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (0)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 1) (serreIntervalGeneratorDegree 1) (0) (by decide)
          (serreIntervalGenerator A 1 ⊗ₜ[A] serreIntervalGenerator A 1)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_one_apply, chain_comp_apply, serreIntervalAugmentation_one_value,
    serreIntervalDiagonal_one_value]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [serreIntervalAugmentation_one_value, one_smul]
  exact serreIntervalDiagonal_one_value A


private lemma max_diagonal_case_12 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (-1)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 1) (serreIntervalGeneratorDegree 2) (-1) (by decide)
          (serreIntervalGenerator A 1 ⊗ₜ[A] serreIntervalGenerator A 2)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (-1)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 1) (serreIntervalGeneratorDegree 2) (-1) (by decide)
          (serreIntervalGenerator A 1 ⊗ₜ[A] serreIntervalGenerator A 2)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_one_apply, chain_comp_apply, serreIntervalAugmentation_edge,
    map_zero, serreIntervalDiagonal_one_value, serreIntervalDiagonal_edge,
    serreIntervalDiagonalEdge, TensorProduct.tmul_add, map_add]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [serreIntervalAugmentation_zero_value, serreIntervalAugmentation_one_value,
    serreIntervalAugmentation_edge, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero,
    smul_zero, add_zero]


private lemma max_diagonal_case_20 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (-1)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 2) (serreIntervalGeneratorDegree 0) (-1) (by decide)
          (serreIntervalGenerator A 2 ⊗ₜ[A] serreIntervalGenerator A 0)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (-1)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 2) (serreIntervalGeneratorDegree 0) (-1) (by decide)
          (serreIntervalGenerator A 2 ⊗ₜ[A] serreIntervalGenerator A 0)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_edge_zero, serreIntervalDiagonal_zero_value,
    serreIntervalDiagonal_edge, serreIntervalDiagonalEdge, TensorProduct.add_tmul, map_add]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [serreIntervalAugmentation_zero_value, one_smul]
  rfl


private lemma max_diagonal_case_21 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (-1)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 2) (serreIntervalGeneratorDegree 1) (-1) (by decide)
          (serreIntervalGenerator A 2 ⊗ₜ[A] serreIntervalGenerator A 1)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (-1)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 2) (serreIntervalGeneratorDegree 1) (-1) (by decide)
          (serreIntervalGenerator A 2 ⊗ₜ[A] serreIntervalGenerator A 1)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_edge_one, map_zero, serreIntervalDiagonal_one_value,
    serreIntervalDiagonal_edge, serreIntervalDiagonalEdge, TensorProduct.add_tmul, map_add]
  simp only [tensorInterchangeMap_apply_of_sums]
  repeat first
    | erw [serreIntervalMax_zero_apply]
    | erw [serreIntervalMax_one_apply]
    | erw [serreIntervalMax_edge_zero]
    | erw [serreIntervalMax_edge_one]
    | erw [serreIntervalMax_edge_edge]
  dsimp
  simp only [serreIntervalAugmentation_one_value, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, map_zero, smul_zero, add_zero]


private lemma max_diagonal_case_22 :
    (serreIntervalMax A ≫ serreIntervalDiagonal A).f (-2)
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 2) (serreIntervalGeneratorDegree 2) (-2) (by decide)
          (serreIntervalGenerator A 2 ⊗ₜ[A] serreIntervalGenerator A 2)) =
      ((serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A)).f (-2)
        (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree 2) (serreIntervalGeneratorDegree 2) (-2) (by decide)
          (serreIntervalGenerator A 2 ⊗ₜ[A] serreIntervalGenerator A 2)) := by
  simp only [chain_comp_apply]
  dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
  rw [tensorMap_apply]
  simp only [serreIntervalMax_edge_edge, map_zero, serreIntervalDiagonal_edge,
    serreIntervalDiagonalEdge, TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
  simp only [tensorInterchangeMap_apply_of_sums]
  erw [serreIntervalMax_edge_edge]
  simp only [TensorProduct.tmul_zero, map_zero, smul_zero, zero_add]
  erw [serreIntervalMax_edge_one]
  simp only [TensorProduct.tmul_zero, map_zero, smul_zero, zero_add]
  erw [serreIntervalMax_one_apply]
  dsimp
  simp only [serreIntervalAugmentation_edge, map_zero, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, smul_zero, add_zero]

/-- 元の max connection は、元の tensor Serre 対角を同じ signed 交差で保存する。 -/
lemma serreIntervalMax_diagonal :
    serreIntervalMax A ≫ serreIntervalDiagonal A =
      (serreIntervalDiagonal A ⊗ₘ serreIntervalDiagonal A) ≫
        tensorμ (serreInterval A) (serreInterval A) (serreInterval A) (serreInterval A) ≫
          (serreIntervalMax A ⊗ₘ serreIntervalMax A) := by
  apply serreIntervalTensor_hom_ext A
  intro i j n hn
  fin_cases i <;> fin_cases j
  all_goals
    first
    | have hn' : n = 0 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -1 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -2 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    rcases hn' with rfl
  · exact max_diagonal_case_00 A
  · exact max_diagonal_case_01 A
  · exact max_diagonal_case_02 A
  · exact max_diagonal_case_10 A
  · exact max_diagonal_case_11 A
  · exact max_diagonal_case_12 A
  · exact max_diagonal_case_20 A
  · exact max_diagonal_case_21 A
  · exact max_diagonal_case_22 A

end SerrePositivity.KST.SConstruction
