module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulStage
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalTowerPresentation

/-! # 一座標Koszul塔の直積の成分計算

次数−1と0の直積を環の列へ同定し、微分と差分を具体的に計算する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]

/-- 一座標Koszul塔の負次数の直積を環の列へ同定する。 -/
def principalKoszulProductNegEquiv (f : R) :
    (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1) ≃ₗ[R] (ℕ → R) :=
  (complexProductDegreeEquiv R _ (-1)).trans
    (LinearEquiv.piCongrRight (fun n ↦ (principalKoszulStageNegIso R f n).toLinearEquiv))

/-- 一座標Koszul塔の零次数の直積を環の列へ同定する。 -/
def principalKoszulProductZeroEquiv (f : R) :
    (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X 0 ≃ₗ[R] (ℕ → R) :=
  (complexProductDegreeEquiv R _ 0).trans
    (LinearEquiv.piCongrRight (fun n ↦ (principalKoszulStageZeroIso R f n).toLinearEquiv))

@[simp] theorem principalKoszulProductNegEquiv_apply (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1)) (n : ℕ) :
    principalKoszulProductNegEquiv R f x n =
      (principalKoszulStageNegIso R f n).hom
        ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x) := by
  simp [principalKoszulProductNegEquiv]
  rfl

@[simp] theorem principalKoszulProductZeroEquiv_apply (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X 0) (n : ℕ) :
    principalKoszulProductZeroEquiv R f x n =
      (principalKoszulStageZeroIso R f n).hom
        ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0 x) := by
  simp [principalKoszulProductZeroEquiv]
  rfl

/-- 直積の微分は、各座標でfの冪を掛ける写像。 -/
theorem principalKoszulProduct_d (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1)) :
    principalKoszulProductZeroEquiv R f
      ((piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).d (-1) 0 x) =
    principalPowerMap R f (principalKoszulProductNegEquiv R f x) := by
  ext n
  rw [principalKoszulProductZeroEquiv_apply]
  have h := congrArg (fun g ↦ g.hom x)
    ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).comm (-1) 0)
  change (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-1) 0
    ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x) =
      (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0
        ((piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).d (-1) 0 x) at h
  rw [← h]
  have hd := congrArg (fun g ↦ g.hom ((Pi.π (powerKoszulTower R
    (fun _ : Fin 1 ↦ f)) n).f (-1) x)) (principalKoszulStage_d R f n)
  simpa [principalPowerMap, principalKoszulProductNegEquiv_apply, smul_eq_mul] using hd

/-- 負次数の直積差分はfによる漸化式。 -/
theorem principalKoszulProductNeg_difference (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1)) :
    principalKoszulProductNegEquiv R f
      ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
        (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f (-1) x) =
    adicRecurrenceMap f (principalKoszulProductNegEquiv R f x) := by
  ext n
  rw [principalKoszulProductNegEquiv_apply]
  have h := congrArg (fun g ↦ (g.f (-1)).hom x)
    (complexTowerDifference_projection R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f)) n)
  change (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1)
    ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f (-1) x) =
    (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x -
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f (-1)
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) (n + 1)).f (-1) x) at h
  rw [h, map_sub]
  have ht := congrArg (fun g ↦ g.hom ((Pi.π (powerKoszulTower R
    (fun _ : Fin 1 ↦ f)) (n + 1)).f (-1) x))
      (principalKoszulStageNeg_transition R f n)
  simpa [adicRecurrenceMap, principalKoszulProductNegEquiv_apply, smul_eq_mul] using
    congrArg (fun y : R ↦ (principalKoszulStageNegIso R f n).hom
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x) - y) ht

/-- 零次数の直積差分は恒等遷移による漸化式。 -/
theorem principalKoszulProductZero_difference (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X 0) :
    principalKoszulProductZeroEquiv R f
      ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
        (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f 0 x) =
    adicRecurrenceMap (1 : R) (principalKoszulProductZeroEquiv R f x) := by
  ext n
  rw [principalKoszulProductZeroEquiv_apply]
  have h := congrArg (fun g ↦ (g.f 0).hom x)
    (complexTowerDifference_projection R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f)) n)
  change (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0
    ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f 0 x) =
    (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0 x -
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f 0
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) (n + 1)).f 0 x) at h
  rw [h, map_sub]
  have ht := congrArg (fun g ↦ g.hom ((Pi.π (powerKoszulTower R
    (fun _ : Fin 1 ↦ f)) (n + 1)).f 0 x))
      (principalKoszulStageZero_transition R f n)
  simpa [adicRecurrenceMap, principalKoszulProductZeroEquiv_apply] using
    congrArg (fun y : R ↦ (principalKoszulStageZeroIso R f n).hom
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0 x) - y) ht

/-- 直積も、一座標Koszul複体の範囲外では零。 -/
theorem principalKoszulProduct_isZero (f : R) (i : ℤ) (hi : i < -1 ∨ 0 < i) :
    IsZero ((piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X i) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ (complexProductDegreeEquiv R _ i).injective ?_⟩
  funext n
  have hn : IsZero ((powerKoszulTower R (fun _ : Fin 1 ↦ f) n).X i) := by
    rcases hi with hi | hi
    · exact koszulComplex_isZero_X_of_lt _ i (by simpa using hi)
    · exact koszulComplex_isZero_X_of_pos _ i hi
  exact (ModuleCat.isZero_iff_subsingleton.mp hn).elim _ _

end SerrePositivity.DerivedCompletion
