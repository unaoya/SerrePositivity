module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleConeCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulProduct

/-! # 二座標Koszul塔の有限段の具体的な成分

末尾dを外側の錐に取る表示を固定し、元のFin 2のKoszul塔との同型を明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- f,dの順の二座標。 -/
def pairKoszulCoordinates (f d : R) : Fin 2 → R := Fin.snoc (fun _ : Fin 1 ↦ f) d

/-- 各冪の二座標Koszul複体の、外側の錐を明示した表示。 -/
def pairKoszulTower (f d : R) (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))

/-- 二座標の各冪は、冪を取った座標を並べた列に一致する。 -/
theorem pairKoszulCoordinates_pow (f d : R) (n : ℕ) :
    (fun i : Fin 2 ↦ pairKoszulCoordinates R f d i ^ n) =
      Fin.snoc (fun _ : Fin 1 ↦ f ^ n) (d ^ n) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · change Fin.snoc (α := fun _ : Fin 2 ↦ R) (fun _ : Fin 1 ↦ f) d (Fin.last 1) ^ n =
      Fin.snoc (α := fun _ : Fin 2 ↦ R) (fun _ : Fin 1 ↦ f ^ n) (d ^ n) (Fin.last 1)
    simp only [Fin.snoc_last]
  · simp [pairKoszulCoordinates]

/-- 元のFin 2の定義と、外側の錐を明示した表示は一致する。 -/
theorem powerKoszulTower_pair_eq (f d : R) (n : ℕ) :
    powerKoszulTower R (pairKoszulCoordinates R f d) n = pairKoszulTower R f d n := by
  change koszulComplex (fun i ↦ pairKoszulCoordinates R f d i ^ n) = _
  rw [pairKoszulCoordinates_pow, koszulComplex_succ, Fin.snoc_last, Fin.init_snoc]
  rfl

/-- 元の有限段から具体的な表示への同型。 -/
def pairKoszulStageIso (f d : R) (n : ℕ) :
    powerKoszulTower R (pairKoszulCoordinates R f d) n ≅ pairKoszulTower R f d n :=
  eqToIso (powerKoszulTower_pair_eq R f d n)

/-- 最低次数の項を、交差境界の係数となるRへ同定する。 -/
def pairKoszulStageNegTwoEquiv (f d : R) (n : ℕ) :
    (pairKoszulTower R f d n).X (-2) ≃ₗ[R] R :=
  (moduleConeFstIso (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
    (-2) (-1) (by decide) (koszulComplex_isZero_X_of_lt _ (-2) (by norm_num))).toLinearEquiv ≪≫ₗ
      (principalKoszulStageNegIso R f n).toLinearEquiv

/-- 次数−1の二つの成分。第一成分はd、第二成分はfに対応する。 -/
def pairKoszulStageNegOneEquiv (f d : R) (n : ℕ) :
    (pairKoszulTower R f d n).X (-1) ≃ₗ[R] R × R :=
  moduleConeDegreeEquiv (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
    (-1) 0 (by decide) ≪≫ₗ
      (principalKoszulStageZeroIso R f n).toLinearEquiv.prodCongr
        (principalKoszulStageNegIso R f n).toLinearEquiv

/-- 零次数の項をRへ同定する。 -/
def pairKoszulStageZeroEquiv (f d : R) (n : ℕ) :
    (pairKoszulTower R f d n).X 0 ≃ₗ[R] R :=
  (moduleConeSndIso (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
    0 1 rfl (koszulComplex_isZero_X_of_pos _ 1 (by norm_num))).toLinearEquiv ≪≫ₗ
      (principalKoszulStageZeroIso R f n).toLinearEquiv

@[simp] theorem pairKoszulStageNegTwoEquiv_apply (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d n).X (-2)) :
    pairKoszulStageNegTwoEquiv R f d n x = (principalKoszulStageNegIso R f n).hom
      (fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
        (-2) (-1) (by decide) x) := rfl

@[simp] theorem pairKoszulStageNegOneEquiv_fst (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d n).X (-1)) :
    (pairKoszulStageNegOneEquiv R f d n x).1 = (principalKoszulStageZeroIso R f n).hom
      (fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
        (-1) 0 (by decide) x) := rfl

@[simp] theorem pairKoszulStageNegOneEquiv_snd (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d n).X (-1)) :
    (pairKoszulStageNegOneEquiv R f d n x).2 = (principalKoszulStageNegIso R f n).hom
      (sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) (-1) x) := rfl

@[simp] theorem pairKoszulStageZeroEquiv_apply (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d n).X 0) :
    pairKoszulStageZeroEquiv R f d n x = (principalKoszulStageZeroIso R f n).hom
      (sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) 0 x) := rfl

/-- 一座標微分を、成分の元で計算する。 -/
theorem principalKoszulStage_d_apply (f : R) (n : ℕ)
    (x : (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).X (-1)) :
    (principalKoszulStageZeroIso R f n).hom
      ((powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-1) 0 x) =
      f ^ n * (principalKoszulStageNegIso R f n).hom x := by
  have h := congrArg (fun g ↦ g.hom x) (principalKoszulStage_d R f n)
  simpa [smul_eq_mul] using h

/-- 最低次数からの微分は、符号付きの交差境界。 -/
theorem pairKoszulStage_d_negTwo (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d n).X (-2)) :
    pairKoszulStageNegOneEquiv R f d n ((pairKoszulTower R f d n).d (-2) (-1) x) =
      (-f ^ n * pairKoszulStageNegTwoEquiv R f d n x,
        d ^ n * pairKoszulStageNegTwoEquiv R f d n x) := by
  apply Prod.ext
  · rw [pairKoszulStageNegOneEquiv_fst]
    have h := congrArg (fun g ↦ g.hom x)
      (d_fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
        (-2) (-1) 0 (by decide) (by decide))
    change fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
      (-1) 0 (by decide) ((pairKoszulTower R f d n).d (-2) (-1) x) =
        -(powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-1) 0
          (fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
            (-2) (-1) (by decide) x) at h
    rw [h, map_neg, principalKoszulStage_d_apply, neg_mul]
    rfl
  · rw [pairKoszulStageNegOneEquiv_snd]
    have h := congrArg (fun g ↦ g.hom x)
      (d_sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
        (-2) (-1) (by decide))
    have hz : sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) (-2) x = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp
        (koszulComplex_isZero_X_of_lt (fun _ : Fin 1 ↦ f ^ n) (-2) (by norm_num))).elim _ _
    change sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) (-1)
      ((pairKoszulTower R f d n).d (-2) (-1) x) =
        d ^ n • fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
          (-2) (-1) (by decide) x +
        (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-2) (-1)
          (sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) (-2) x) at h
    rw [hz, map_zero, add_zero] at h
    rw [h, map_smul]
    rfl

/-- 零次数への微分は、二つの冪の作用の和。 -/
theorem pairKoszulStage_d_negOne (f d : R) (n : ℕ)
    (x : (pairKoszulTower R f d n).X (-1)) :
    pairKoszulStageZeroEquiv R f d n ((pairKoszulTower R f d n).d (-1) 0 x) =
      d ^ n * (pairKoszulStageNegOneEquiv R f d n x).1 +
        f ^ n * (pairKoszulStageNegOneEquiv R f d n x).2 := by
  rw [pairKoszulStageZeroEquiv_apply]
  have h := congrArg (fun g ↦ g.hom x)
    (d_sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
      (-1) 0 (by decide))
  change sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) 0
    ((pairKoszulTower R f d n).d (-1) 0 x) =
      d ^ n • fstX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))
        (-1) 0 (by decide) x +
      (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-1) 0
        (sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) (-1) x) at h
  rw [h, map_add, map_smul, principalKoszulStage_d_apply]
  rfl

end SerrePositivity.DerivedCompletion
