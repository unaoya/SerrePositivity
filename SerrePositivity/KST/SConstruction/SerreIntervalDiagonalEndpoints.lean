module
public import SerrePositivity.KST.SConstruction.SerreIntervalDiagonal

/-! # Serre 対角の元の一頂点の保存
概要：辺の像の微分から、一頂点も元の二重 tensor へ写ることを証明する。
方針：tensor 微分の Leibniz 則と元の辺の境界を使い、二つの交差項を消す。
規約：Serre 対角の非対称な因子順を保持する。使われ方：余結合律と余単位律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

private lemma tensor_d_apply {A : Type u} [CommRing A] (P Q : Complex A)
    (i j n : ℤ) (h : i + j = n) (x : P.X i) (y : Q.X j) :
    (P ⊗ Q).d n (n + 1) (ιTensorObj P Q i j n h (x ⊗ₜ[A] y)) =
      ιTensorObj P Q (i + 1) j (n + 1) (by omega) (P.d i (i + 1) x ⊗ₜ[A] y) +
      i.negOnePow • ιTensorObj P Q i (j + 1) (n + 1) (by omega)
        (x ⊗ₜ[A] Q.d j (j + 1) y) :=
  SerrePositivity.cochainTensor_d_apply_ι P Q i j n h x y

variable (A : Type u) [CommRing A]

/-- Serre 対角の元の辺の像の微分は、一頂点の二重 tensor と零頂点のそれとの差。 -/
lemma serreIntervalDiagonalEdge_d :
    (serreInterval A ⊗ serreInterval A).d (-1) 0 (serreIntervalDiagonalEdge A) =
      ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
          ((cycleFromUnit _ (serreIntervalOne A)).val ⊗ₜ[A]
            (cycleFromUnit _ (serreIntervalOne A)).val) -
        ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
          ((cycleFromUnit _ (serreIntervalZero A)).val ⊗ₜ[A]
            (cycleFromUnit _ (serreIntervalZero A)).val) := by
  have h₀ := (cycleFromUnit _ (serreIntervalZero A)).property
  have h₁ := (cycleFromUnit _ (serreIntervalOne A)).property
  change (serreInterval A).d 0 1 (cycleFromUnit _ (serreIntervalZero A)).val = 0 at h₀
  change (serreInterval A).d 0 1 (cycleFromUnit _ (serreIntervalOne A)).val = 0 at h₁
  unfold serreIntervalDiagonalEdge
  rw [map_add]
  have hL := tensor_d_apply (serreInterval A) (serreInterval A) 0 (-1) (-1) (by omega)
    (cycleFromUnit _ (serreIntervalZero A)).val (serreIntervalEdge A)
  have hR := tensor_d_apply (serreInterval A) (serreInterval A) (-1) 0 (-1) (by omega)
    (serreIntervalEdge A) (cycleFromUnit _ (serreIntervalOne A)).val
  refine (congrArg₂ (fun x y : (serreInterval A ⊗ serreInterval A).X 0 => x + y) hL hR).trans ?_
  change ιTensorObj (serreInterval A) (serreInterval A) 1 (-1) 0 (by omega)
        ((serreInterval A).d 0 1 (cycleFromUnit _ (serreIntervalZero A)).val ⊗ₜ[A]
          serreIntervalEdge A) +
      (0 : ℤ).negOnePow • ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
        ((cycleFromUnit _ (serreIntervalZero A)).val ⊗ₜ[A]
          (serreInterval A).d (-1) 0 (serreIntervalEdge A)) +
      (ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
        ((serreInterval A).d (-1) 0 (serreIntervalEdge A) ⊗ₜ[A]
          (cycleFromUnit _ (serreIntervalOne A)).val) +
      (-1 : ℤ).negOnePow • ιTensorObj (serreInterval A) (serreInterval A) (-1) 1 0 (by omega)
        (serreIntervalEdge A ⊗ₜ[A]
          (serreInterval A).d 0 1 (cycleFromUnit _ (serreIntervalOne A)).val)) = _
  simp only [h₀, h₁, serreIntervalEdge_d, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    map_zero, smul_zero, zero_add, add_zero, Int.negOnePow_zero, one_smul]
  rw [TensorProduct.tmul_sub, TensorProduct.sub_tmul]
  simp only [map_sub]
  abel

/-- Serre 対角は元の一頂点も、その同じ二重 tensor へ写す。 -/
lemma serreIntervalDiagonal_one :
    serreIntervalOne A ≫ serreIntervalDiagonal A =
      (λ_ (𝟙_ (Complex A))).inv ≫ (serreIntervalOne A ⊗ₘ serreIntervalOne A) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (serreIntervalOne A ≫ serreIntervalLift A _ _)).val = _
  rw [serreIntervalLift_one_cycle, serreIntervalDiagonalEdge_d]
  change (((λ_ (𝟙_ (Complex A))).inv ≫
      (serreIntervalZero A ⊗ₘ serreIntervalZero A)).f 0) (1 : A) + _ =
    (((λ_ (𝟙_ (Complex A))).inv ≫
      (serreIntervalOne A ⊗ₘ serreIntervalOne A)).f 0) (1 : A)
  rw [unit_tensor_apply, unit_tensor_apply]
  abel

/-- Serre 対角の零頂点の斉次値は、元の二つの零頂点の tensor。 -/
lemma serreIntervalDiagonal_zero_value :
    (serreIntervalDiagonal A).f 0 (cycleFromUnit _ (serreIntervalZero A)).val =
      ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
        ((cycleFromUnit _ (serreIntervalZero A)).val ⊗ₜ[A]
          (cycleFromUnit _ (serreIntervalZero A)).val) := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalDiagonal_zero A)
  exact h.trans (unit_tensor_apply _ _)

/-- Serre 対角の一頂点の斉次値は、元の二つの一頂点の tensor。 -/
lemma serreIntervalDiagonal_one_value :
    (serreIntervalDiagonal A).f 0 (cycleFromUnit _ (serreIntervalOne A)).val =
      ιTensorObj (serreInterval A) (serreInterval A) 0 0 0 rfl
        ((cycleFromUnit _ (serreIntervalOne A)).val ⊗ₜ[A]
          (cycleFromUnit _ (serreIntervalOne A)).val) := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (serreIntervalDiagonal_one A)
  exact h.trans (unit_tensor_apply _ _)

end SerrePositivity.KST.SConstruction
