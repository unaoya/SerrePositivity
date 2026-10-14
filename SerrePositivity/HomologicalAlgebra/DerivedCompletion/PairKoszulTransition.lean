module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairKoszulStage
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleConeNaturality

/-! # 二座標Koszul塔の遷移の行列

外側の錐の写像を各射影で計算し、三つの次数の遷移を明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 二座標の遷移を誘導する可換正方形。 -/
def pairKoszulTransitionArrow (f d : R) (n : ℕ) :
    Arrow.mk (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1))) ⟶
      Arrow.mk (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) :=
  Arrow.homMk (d • powerKoszulTransition R (fun _ : Fin 1 ↦ f) n)
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n) (by
      simp [smulId, pow_succ, Linear.comp_smul, Linear.smul_comp, smul_smul, mul_comm])

/-- dの外側の錐に沿う、二座標の正規化した遷移写像。 -/
def pairKoszulTransition (f d : R) (n : ℕ) :
    pairKoszulTower R f d (n + 1) ⟶ pairKoszulTower R f d n :=
  mapArrowHom
    (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)))
    (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) (fun j ↦ ⟨j - 1, by simp⟩)
    (pairKoszulTransitionArrow R f d n)

/-- 一座標の負次数遷移を、成分の元で計算する。 -/
theorem principalKoszulStageNeg_transition_apply (f : R) (n : ℕ)
    (x : (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)).X (-1)) :
    (principalKoszulStageNegIso R f n).hom
      ((powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f (-1) x) =
      f * (principalKoszulStageNegIso R f (n + 1)).hom x := by
  have h := congrArg (fun g ↦ g.hom x) (principalKoszulStageNeg_transition R f n)
  simpa [smul_eq_mul] using h

/-- 一座標の零次数遷移を、成分の元で計算する。 -/
theorem principalKoszulStageZero_transition_apply (f : R) (n : ℕ)
    (x : (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)).X 0) :
    (principalKoszulStageZeroIso R f n).hom
      ((powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f 0 x) =
      (principalKoszulStageZeroIso R f (n + 1)).hom x :=
  congrArg (fun g ↦ g.hom x) (principalKoszulStageZero_transition R f n)

/-- 最低次数の遷移はfd倍。 -/
theorem pairKoszulStageNegTwo_transition (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d (n + 1)).X (-2)) :
    pairKoszulStageNegTwoEquiv R f d n ((pairKoszulTransition R f d n).f (-2) x) =
      (f * d) * pairKoszulStageNegTwoEquiv R f d (n + 1) x := by
  rw [pairKoszulStageNegTwoEquiv_apply]
  have h := congrArg (fun g ↦ g.hom x)
    (moduleConeArrowMap_fst
      (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)))
      (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
      (pairKoszulTransitionArrow R f d n)
      (-2) (-1) (by decide))
  change fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
    (-2) (-1) (by decide) ((pairKoszulTransition R f d n).f (-2) x) =
      d • (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f (-1)
        (fstX (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)))
          (-2) (-1) (by decide) x) at h
  rw [h, map_smul, principalKoszulStageNeg_transition_apply, pairKoszulStageNegTwoEquiv_apply]
  change d * (f * _) = (f * d) * _
  ring

/-- 次数−1の遷移は、d倍とf倍の対角行列。 -/
theorem pairKoszulStageNegOne_transition (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d (n + 1)).X (-1)) :
    pairKoszulStageNegOneEquiv R f d n ((pairKoszulTransition R f d n).f (-1) x) =
      (d * (pairKoszulStageNegOneEquiv R f d (n + 1) x).1,
        f * (pairKoszulStageNegOneEquiv R f d (n + 1) x).2) := by
  apply Prod.ext
  · rw [pairKoszulStageNegOneEquiv_fst]
    have h := congrArg (fun g ↦ g.hom x)
      (moduleConeArrowMap_fst
        (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)))
        (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
        (pairKoszulTransitionArrow R f d n)
        (-1) 0 (by decide))
    change fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
      (-1) 0 (by decide) ((pairKoszulTransition R f d n).f (-1) x) =
        d • (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f 0
          (fstX (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)))
            (-1) 0 (by decide) x) at h
    rw [h, map_smul, principalKoszulStageZero_transition_apply]
    rfl
  · rw [pairKoszulStageNegOneEquiv_snd]
    have h := congrArg (fun g ↦ g.hom x)
      (moduleConeArrowMap_snd
        (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)))
        (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
        (pairKoszulTransitionArrow R f d n) (-1))
    change sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) (-1)
      ((pairKoszulTransition R f d n).f (-1) x) =
        (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f (-1)
          (sndX (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1))) (-1) x) at h
    rw [h, principalKoszulStageNeg_transition_apply]
    rfl

/-- 零次数の遷移は恒等。 -/
theorem pairKoszulStageZero_transition (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d (n + 1)).X 0) :
    pairKoszulStageZeroEquiv R f d n ((pairKoszulTransition R f d n).f 0 x) =
      pairKoszulStageZeroEquiv R f d (n + 1) x := by
  rw [pairKoszulStageZeroEquiv_apply]
  have h := congrArg (fun g ↦ g.hom x)
    (moduleConeArrowMap_snd
      (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1)))
      (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
      (pairKoszulTransitionArrow R f d n) 0)
  change sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) 0
    ((pairKoszulTransition R f d n).f 0 x) =
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f 0
        (sndX (smulId (d ^ (n + 1)) (powerKoszulTower R (fun _ : Fin 1 ↦ f) (n + 1))) 0 x) at h
  rw [h, principalKoszulStageZero_transition_apply]
  rfl

end SerrePositivity.DerivedCompletion
