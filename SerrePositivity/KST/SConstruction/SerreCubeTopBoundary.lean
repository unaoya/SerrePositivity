module
public import SerrePositivity.KST.SConstruction.SerreCubeBoundaryTensor

/-! # 元の最高生成元の符号付き全面境界
概要：元の Serre 鎖立方体の最高生成元の微分を、元の一面と零面の差の有限和で表す。
方針：右端の二面と内側の全ての面への分解を、元の辺付加の線形性で帰納する。
規約：座標 i の符号は左側の辺の個数 n−i による。使われ方：native HA の符号照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped BigOperators
variable (A : Type u) [CommRing A]

/-- 元の最高生成元への、同じ座標の一面と零面の差。 -/
def serreCubeTopFaceDifference (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeComplex A (n + 1)).X (-(n : ℤ)) :=
  (serreCubeFace A true n i).hom.f (-(n : ℤ)) (serreCubeTopCell A n) -
    (serreCubeFace A false n i).hom.f (-(n : ℤ)) (serreCubeTopCell A n)

/-- 元の内側の二面の差は、同じ一段小さい二面の差への元の辺付加。 -/
lemma serreCubeTopFaceDifference_succ (n : ℕ) (i : Fin (n + 1)) :
    serreCubeTopFaceDifference A (n + 1) i.succ =
      serreCubeAppendEdge A (n + 1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
        (serreCubeTopFaceDifference A n i) := by
  have h := congrArg₂ (fun x y => x - y)
    (serreCubeFace_succ_apply A true n i (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ))
      (by omega) (serreCubeTopCell A n) (serreIntervalEdge A))
    (serreCubeFace_succ_apply A false n i (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ))
      (by omega) (serreCubeTopCell A n) (serreIntervalEdge A))
  exact h.trans ((serreCubeAppendEdge A (n + 1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ))
    (by omega)).map_sub _ _).symm

/-- 元の全面の符号付き和。右端からの座標の左側の辺の個数を符号に使う。 -/
def serreCubeTopFaceBoundary (n : ℕ) : (serreCubeComplex A (n + 1)).X (-(n : ℤ)) :=
  ∑ i : Fin (n + 1), ((n : ℤ) - (i.val : ℤ)).negOnePow • serreCubeTopFaceDifference A n i

/-- 元の全面境界の零次元は、同じ鎖区間の二端点差。 -/
lemma serreCubeTopFaceBoundary_zero :
    serreCubeTopFaceBoundary A 0 = serreCubeTopFaceDifference A 0 0 := by
  change (∑ i : Fin 1, ((0 : ℤ) - (i.val : ℤ)).negOnePow •
    serreCubeTopFaceDifference A 0 i) = _
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, Int.natCast_zero, sub_zero, Int.negOnePow_zero, one_smul]

/-- 元の全面境界は、内側の全面への元の辺付加と、右端の符号付き二面に分解する。 -/
lemma serreCubeTopFaceBoundary_succ (n : ℕ) :
    serreCubeTopFaceBoundary A (n + 1) =
      serreCubeAppendEdge A (n + 1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
          (serreCubeTopFaceBoundary A n) +
        (-((n + 1 : ℕ) : ℤ)).negOnePow • serreCubeTopFaceDifference A (n + 1) 0 := by
  have hs :
      (∑ i : Fin (n + 1),
        (((n + 1 : ℕ) : ℤ) - (i.succ.val : ℤ)).negOnePow •
          serreCubeTopFaceDifference A (n + 1) i.succ) =
      serreCubeAppendEdge A (n + 1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
        (serreCubeTopFaceBoundary A n) := by
    rw [serreCubeTopFaceBoundary, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (((n + 1 : ℕ) : ℤ) - (i.succ.val : ℤ)) =
      (n : ℤ) - (i.val : ℤ) by
        have hi : i.succ.val = i.val + 1 := rfl
        omega, serreCubeTopFaceDifference_succ]
    simp only [Units.smul_def, map_zsmul]
  change (∑ i : Fin (n + 2),
    (((n + 1 : ℕ) : ℤ) - (i.val : ℤ)).negOnePow •
      serreCubeTopFaceDifference A (n + 1) i) = _
  rw [Fin.sum_univ_succ, hs]
  simp only [Fin.val_zero, Int.natCast_zero, sub_zero, Int.negOnePow_neg]
  exact add_comm _ _

/-- 元の一次元の最高生成元の微分は、元の二面の差。 -/
lemma serreCubeTopCell_one_d :
    (serreCubeComplex A 1).d (-1) 0 (serreCubeTopCell A 1) =
      serreCubeTopFaceBoundary A 0 := by
  have h := serreTensorDifferential_apply A (serreCubeComplex A 0) (serreInterval A)
    0 1 (-1) 0 (-1) 0 rfl rfl rfl rfl (serreCubeTopCell A 0) (serreIntervalEdge A)
  have hz : ιTensorObj (serreCubeComplex A 0) (serreInterval A) 1 (-1) 0 rfl
      ((serreCubeComplex A 0).d 0 1 (serreCubeTopCell A 0) ⊗ₜ[A] serreIntervalEdge A) = 0 :=
    (congrArg (fun z => ιTensorObj (serreCubeComplex A 0) (serreInterval A) 1 (-1) 0 rfl
      (z ⊗ₜ[A] serreIntervalEdge A)) (serreCubeTopCell_zero_d A)).trans (by
        simp only [TensorProduct.zero_tmul, map_zero])
  have h' : (serreCubeComplex A 1).d (-1) 0 (serreCubeTopCell A 1) =
      ιTensorObj (serreCubeComplex A 0) (serreInterval A) 0 0 0 rfl
        (serreCubeTopCell A 0 ⊗ₜ[A]
          ((cycleFromUnit _ (serreIntervalOne A)).val -
            (cycleFromUnit _ (serreIntervalZero A)).val)) := by
    change (serreCubeComplex A 0 ⊗ serreInterval A).d (-1) 0
      (ιTensorObj (serreCubeComplex A 0) (serreInterval A) 0 (-1) (-1) rfl
        (serreCubeTopCell A 0 ⊗ₜ[A] serreIntervalEdge A)) = _
    simpa only [hz, zero_add, Int.negOnePow_zero, one_smul, serreIntervalEdge_d] using h
  exact h'.trans ((serreCubeTopCell_face_zero_difference A 0).symm.trans
    (serreCubeTopFaceBoundary_zero A).symm)

/-- 元の全正次元の最高生成元の微分は、元の全座標の符号付き二面の差の和。 -/
lemma serreCubeTopCell_d (n : ℕ) :
    (serreCubeComplex A (n + 1)).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (serreCubeTopCell A (n + 1)) = serreCubeTopFaceBoundary A n := by
  induction n with
  | zero => exact serreCubeTopCell_one_d A
  | succ n ih =>
    exact (serreCubeTopCell_succ_succ_d A n).trans
      ((congrArg (fun x =>
        serreCubeAppendEdge A (n + 1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega) x +
          (-((n + 1 : ℕ) : ℤ)).negOnePow • serreCubeTopFaceDifference A (n + 1) 0)
        ih).trans (serreCubeTopFaceBoundary_succ A n).symm)

end SerrePositivity.KST.SConstruction
