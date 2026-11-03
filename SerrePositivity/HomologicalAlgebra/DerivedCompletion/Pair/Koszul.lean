module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Maps
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction

/-! # 二つの座標の Koszul 完備化の H⁰ の環

## 概要

二つの座標の Koszul 塔の有限段を、末尾の座標を外側の錐に取る表示で具体化し（`pairKoszulCoordinates`・`pairKoszulStageIso`）、遷移・直積・完備化の短複体・標準写像を行列で計算する。三項模型の反映から完備化の H⁰ `PairCompletionH0` の環構造と普遍性（`pairCompletionCommRing`・`pairCompletionUnitRingHom`）を与える。

## 方針

元の `Fin 2` の Koszul 塔との同型を明示し、行列の成分で比べる。

## 規約

`pairKoszulCoordinates`・`PairCompletionH0`・`pairCompletionCommRing`・`pairCompletionUnitRingHom` は BhattScholze が使うので名前を変えない（2b の B で定義を一つの座標の反復の側へ移す候補）。旧 `PairKoszul{Stage, Transition, Comparison, Product, Cone, Unit, Ring}`。

## 使われ方

`Pair/Iteration`、`PDCompletion`、`CompletedAlgebraH0`、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section PairKoszulStagePart

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

end PairKoszulStagePart

section PairKoszulTransitionPart

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

end PairKoszulTransitionPart

section PairKoszulComparisonPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category
variable (R : Type u) [CommRing R]

/-- 有限段の表示同型は、元のKoszul遷移と可換する。 -/
theorem pairKoszulStageIso_naturality (f d : R) (n : ℕ) :
    (pairKoszulStageIso R f d (n + 1)).hom ≫ pairKoszulTransition R f d n =
      powerKoszulTransition R (pairKoszulCoordinates R f d) n ≫
        (pairKoszulStageIso R f d n).hom := by
  simp only [pairKoszulStageIso, pairKoszulTower, powerKoszulTower,
    koszulComplex_succ, eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  simp only [powerKoszulTransition, pairKoszulTransition, pairKoszulTransitionArrow,
    koszulComplexMapOfMul, pairKoszulCoordinates,
    Fin.snoc_last, Fin.init_snoc]
  rfl

/-- 二座標塔の具体的な錐表示による、実際のホモトピー逆極限。 -/
def pairKoszulCompletionComplex (f d : R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  complexTowerHomotopyLimit R (pairKoszulTower R f d) (pairKoszulTransition R f d)

/-- 元のKoszul完備化複体と具体的な塔表示の完備化複体との同型。
有限段のH⁰だけの比較ではなく、直積・mapping cone・シフト全体を比較する。 -/
def pairKoszulCompletionIso (f d : R) :
    koszulCompletionComplex R (pairKoszulCoordinates R f d) ≅ pairKoszulCompletionComplex R f d :=
  complexTowerHomotopyLimitIso R (powerKoszulTransition R (pairKoszulCoordinates R f d))
    (pairKoszulTransition R f d) (pairKoszulStageIso R f d)
      (fun n ↦ (pairKoszulStageIso_naturality R f d n).symm)

end SerrePositivity.DerivedCompletion

end PairKoszulComparisonPart

section PairKoszulProductPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- 対の列を、二つの列の対へ並べ替える。 -/
def sequencePairEquiv : (ℕ → R × R) ≃ₗ[R] ((ℕ → R) × (ℕ → R)) where
  toFun x := (fun n ↦ (x n).1, fun n ↦ (x n).2)
  invFun x n := (x.1 n, x.2 n)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 二座標塔の直積。 -/
abbrev pairKoszulProduct (f d : R) := piObj (pairKoszulTower R f d)

/-- 二座標塔の直積の差分。 -/
abbrev pairKoszulDifference (f d : R) :=
  complexTowerDifference R (pairKoszulTower R f d) (pairKoszulTransition R f d)

/-- 直積の最低次数を列へ同定する。 -/
def pairKoszulProductNegTwoEquiv (f d : R) :
    (pairKoszulProduct R f d).X (-2) ≃ₗ[R] (ℕ → R) :=
  complexProductDegreeEquiv R _ (-2) ≪≫ₗ
    LinearEquiv.piCongrRight (fun n ↦ pairKoszulStageNegTwoEquiv R f d n)

/-- 直積の次数−1を二つの列へ同定する。 -/
def pairKoszulProductNegOneEquiv (f d : R) :
    (pairKoszulProduct R f d).X (-1) ≃ₗ[R] ((ℕ → R) × (ℕ → R)) :=
  complexProductDegreeEquiv R _ (-1) ≪≫ₗ
    LinearEquiv.piCongrRight (fun n ↦ pairKoszulStageNegOneEquiv R f d n) ≪≫ₗ
      sequencePairEquiv R

/-- 直積の零次数を列へ同定する。 -/
def pairKoszulProductZeroEquiv (f d : R) :
    (pairKoszulProduct R f d).X 0 ≃ₗ[R] (ℕ → R) :=
  complexProductDegreeEquiv R _ 0 ≪≫ₗ
    LinearEquiv.piCongrRight (fun n ↦ pairKoszulStageZeroEquiv R f d n)

@[simp] theorem pairKoszulProductNegTwoEquiv_apply (f d : R)
    (x : (pairKoszulProduct R f d).X (-2)) (n : ℕ) :
    pairKoszulProductNegTwoEquiv R f d x n = pairKoszulStageNegTwoEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) (-2) x n) := rfl

@[simp] theorem pairKoszulProductNegOneEquiv_fst (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) (n : ℕ) :
    (pairKoszulProductNegOneEquiv R f d x).1 n = (pairKoszulStageNegOneEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) (-1) x n)).1 := rfl

@[simp] theorem pairKoszulProductNegOneEquiv_snd (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) (n : ℕ) :
    (pairKoszulProductNegOneEquiv R f d x).2 n = (pairKoszulStageNegOneEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) (-1) x n)).2 := rfl

@[simp] theorem pairKoszulProductZeroEquiv_apply (f d : R)
    (x : (pairKoszulProduct R f d).X 0) (n : ℕ) :
    pairKoszulProductZeroEquiv R f d x n = pairKoszulStageZeroEquiv R f d n
      (complexProductDegreeEquiv R (pairKoszulTower R f d) 0 x n) := rfl

/-- 直積の最低次数の微分も、符号付きの交差境界。 -/
theorem pairKoszulProduct_d_negTwo (f d : R)
    (x : (pairKoszulProduct R f d).X (-2)) :
    pairKoszulProductNegOneEquiv R f d ((pairKoszulProduct R f d).d (-2) (-1) x) =
      (-principalPowerMap R f (pairKoszulProductNegTwoEquiv R f d x),
        principalPowerMap R d (pairKoszulProductNegTwoEquiv R f d x)) := by
  apply Prod.ext
  · funext n
    rw [pairKoszulProductNegOneEquiv_fst, complexProductDegreeEquiv_d,
      pairKoszulStage_d_negTwo]
    simp [principalPowerMap]
  · funext n
    rw [pairKoszulProductNegOneEquiv_snd, complexProductDegreeEquiv_d,
      pairKoszulStage_d_negTwo]
    rfl

/-- 直積の零次数への微分は、二つの冪による作用の和。 -/
theorem pairKoszulProduct_d_negOne (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) :
    pairKoszulProductZeroEquiv R f d ((pairKoszulProduct R f d).d (-1) 0 x) =
      principalPowerMap R d (pairKoszulProductNegOneEquiv R f d x).1 +
        principalPowerMap R f (pairKoszulProductNegOneEquiv R f d x).2 := by
  funext n
  rw [pairKoszulProductZeroEquiv_apply, complexProductDegreeEquiv_d, pairKoszulStage_d_negOne]
  rfl

/-- 直積の最低次数の差分はfdの漸化式。 -/
theorem pairKoszulProductNegTwo_difference (f d : R)
    (x : (pairKoszulProduct R f d).X (-2)) :
    pairKoszulProductNegTwoEquiv R f d ((pairKoszulDifference R f d).f (-2) x) =
      adicRecurrenceMap (f * d) (pairKoszulProductNegTwoEquiv R f d x) := by
  funext n
  rw [pairKoszulProductNegTwoEquiv_apply, complexProductDegreeEquiv_difference,
    map_sub, pairKoszulStageNegTwo_transition]
  rfl

/-- 直積の次数−1の差分は、dとfの二つの漸化式。 -/
theorem pairKoszulProductNegOne_difference (f d : R)
    (x : (pairKoszulProduct R f d).X (-1)) :
    pairKoszulProductNegOneEquiv R f d ((pairKoszulDifference R f d).f (-1) x) =
      (adicRecurrenceMap d (pairKoszulProductNegOneEquiv R f d x).1,
        adicRecurrenceMap f (pairKoszulProductNegOneEquiv R f d x).2) := by
  apply Prod.ext
  · funext n
    rw [pairKoszulProductNegOneEquiv_fst, complexProductDegreeEquiv_difference,
      map_sub, pairKoszulStageNegOne_transition]
    rfl
  · funext n
    rw [pairKoszulProductNegOneEquiv_snd, complexProductDegreeEquiv_difference,
      map_sub, pairKoszulStageNegOne_transition]
    rfl

/-- 直積の零次数の差分は恒等遷移の漸化式。 -/
theorem pairKoszulProductZero_difference (f d : R)
    (x : (pairKoszulProduct R f d).X 0) :
    pairKoszulProductZeroEquiv R f d ((pairKoszulDifference R f d).f 0 x) =
      adicRecurrenceMap (1 : R) (pairKoszulProductZeroEquiv R f d x) := by
  funext n
  rw [pairKoszulProductZeroEquiv_apply, complexProductDegreeEquiv_difference,
    map_sub, pairKoszulStageZero_transition]
  simp [adicRecurrenceMap]

/-- 直積は二座標Koszul複体の次数の範囲外では零。 -/
theorem pairKoszulProduct_isZero (f d : R) (i : ℤ) (hi : i < -2 ∨ 0 < i) :
    IsZero ((pairKoszulProduct R f d).X i) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ (complexProductDegreeEquiv R _ i).injective ?_⟩
  funext n
  have hn : IsZero ((pairKoszulTower R f d n).X i) := by
    rw [← powerKoszulTower_pair_eq]
    rcases hi with hi | hi
    · exact koszulComplex_isZero_X_of_lt _ i (by simpa using hi)
    · exact koszulComplex_isZero_X_of_pos _ i hi
  exact (ModuleCat.isZero_iff_subsingleton.mp hn).elim _ _

end SerrePositivity.DerivedCompletion

end PairKoszulProductPart

section PairKoszulConePart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 外側の錐の次数−1を、三つの境界変数へ同定する。 -/
def pairCompletionNegEquiv (f d : R) :
    (pairKoszulCompletionComplex R f d).X (-1) ≃ₗ[R]
      (((ℕ → R) × (ℕ → R)) × (ℕ → R)) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) (-1) (-2) (by norm_num)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (pairKoszulDifference R f d) (-2) (-1) (by decide) ≪≫ₗ
      (pairKoszulProductNegOneEquiv R f d).prodCongr (pairKoszulProductNegTwoEquiv R f d)

/-- 外側の錐の次数0を、サイクルの三つの列へ同定する。 -/
def pairCompletionZeroEquiv (f d : R) :
    (pairKoszulCompletionComplex R f d).X 0 ≃ₗ[R]
      ((ℕ → R) × ((ℕ → R) × (ℕ → R))) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 0 (-1) (by norm_num)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (pairKoszulDifference R f d) (-1) 0 (by decide) ≪≫ₗ
      (pairKoszulProductZeroEquiv R f d).prodCongr (pairKoszulProductNegOneEquiv R f d) ≪≫ₗ
        (LinearEquiv.refl R (ℕ → R)).prodCongr (LinearEquiv.neg R)

/-- 外側の錐の次数1を、サイクルの障害となる列へ同定する。 -/
def pairCompletionOneEquiv (f d : R) :
    (pairKoszulCompletionComplex R f d).X 1 ≃ₗ[R] (ℕ → R) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 1 0 (by norm_num)).toLinearEquiv ≪≫ₗ
    (moduleConeSndIso (pairKoszulDifference R f d) 0 1 rfl
      (pairKoszulProduct_isZero R f d 1 (Or.inr (by norm_num)))).toLinearEquiv ≪≫ₗ
        pairKoszulProductZeroEquiv R f d ≪≫ₗ LinearEquiv.neg R

@[simp] theorem pairCompletionNegEquiv_fst (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X (-1)) :
    (pairCompletionNegEquiv R f d x).1 = pairKoszulProductNegOneEquiv R f d
      (fstX (pairKoszulDifference R f d) (-2) (-1) (by decide) x) := rfl

@[simp] theorem pairCompletionNegEquiv_snd (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X (-1)) :
    (pairCompletionNegEquiv R f d x).2 = pairKoszulProductNegTwoEquiv R f d
      (sndX (pairKoszulDifference R f d) (-2) x) := rfl

@[simp] theorem pairCompletionZeroEquiv_fst (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 0) :
    (pairCompletionZeroEquiv R f d x).1 = pairKoszulProductZeroEquiv R f d
      (fstX (pairKoszulDifference R f d) (-1) 0 (by decide) x) := rfl

@[simp] theorem pairCompletionZeroEquiv_snd (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 0) :
    (pairCompletionZeroEquiv R f d x).2 = -pairKoszulProductNegOneEquiv R f d
      (sndX (pairKoszulDifference R f d) (-1) x) := rfl

@[simp] theorem pairCompletionOneEquiv_apply (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 1) :
    pairCompletionOneEquiv R f d x = -pairKoszulProductZeroEquiv R f d
      (sndX (pairKoszulDifference R f d) 0 x) := rfl

/-- 一段シフトした微分の負号。 -/
theorem pairCompletion_d_eq (f d : R) (i j : ℤ) :
    (pairKoszulCompletionComplex R f d).d i j =
      -HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (i + -1) (j + -1) := by
  change (-1 : ℤ).negOnePow • _ = -_
  simp
  rfl

/-- 最低次数からの微分は、交差変数を含む行列モデルの境界。 -/
theorem pairCompletion_d_neg (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X (-1)) :
    pairCompletionZeroEquiv R f d ((pairKoszulCompletionComplex R f d).d (-1) 0 x) =
      pairTowerBoundaryTriple R f d (pairCompletionNegEquiv R f d x) := by
  apply Prod.ext
  · rw [pairCompletionZeroEquiv_fst]
    have h := congrArg (fun g ↦ g.hom x)
      (d_fstX (pairKoszulDifference R f d) (-2) (-1) 0 (by decide) (by decide))
    rw [pairCompletion_d_eq]
    change pairKoszulProductZeroEquiv R f d
      (fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
        (-HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x)) = _
    rw [map_neg, map_neg]
    change fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
      (HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x) =
        -(pairKoszulProduct R f d).d (-1) 0
          (fstX (pairKoszulDifference R f d) (-2) (-1) (by decide) x) at h
    rw [h, map_neg, neg_neg, pairKoszulProduct_d_negOne]
    rfl
  · rw [pairCompletionZeroEquiv_snd]
    have h := congrArg (fun g : (CochainComplex.mappingCone (pairKoszulDifference R f d)).X (-2) ⟶
        (pairKoszulProduct R f d).X (-1) ↦ g.hom x)
      (d_sndX (pairKoszulDifference R f d) (-2) (-1) (by decide))
    rw [pairCompletion_d_eq]
    change -pairKoszulProductNegOneEquiv R f d
      (sndX (pairKoszulDifference R f d) (-1)
        (-HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x)) = _
    rw [map_neg, map_neg, neg_neg]
    change sndX (pairKoszulDifference R f d) (-1)
      (HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-2) (-1) x) =
        (pairKoszulDifference R f d).f (-1)
          (fstX (pairKoszulDifference R f d) (-2) (-1) (by decide) x) +
        (pairKoszulProduct R f d).d (-2) (-1)
          (sndX (pairKoszulDifference R f d) (-2) x) at h
    rw [h, map_add, pairKoszulProductNegOne_difference, pairKoszulProduct_d_negTwo]
    simp [pairTowerBoundaryTriple, pairCompletionNegEquiv_fst, pairCompletionNegEquiv_snd,
      sub_eq_add_neg]

/-- 零次数からの微分は、行列モデルのサイクル条件。 -/
theorem pairCompletion_d_zero (f d : R)
    (x : (pairKoszulCompletionComplex R f d).X 0) :
    pairCompletionOneEquiv R f d ((pairKoszulCompletionComplex R f d).d 0 1 x) =
      pairTowerObstruction R f d (pairCompletionZeroEquiv R f d x) := by
  rw [pairCompletionOneEquiv_apply, pairCompletion_d_eq]
  change -pairKoszulProductZeroEquiv R f d
    (sndX (pairKoszulDifference R f d) 0
      (-HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-1) 0 x)) = _
  rw [map_neg, map_neg, neg_neg]
  have h := congrArg (fun g : (CochainComplex.mappingCone (pairKoszulDifference R f d)).X (-1) ⟶
      (pairKoszulProduct R f d).X 0 ↦ g.hom x)
    (d_sndX (pairKoszulDifference R f d) (-1) 0 (by decide))
  change sndX (pairKoszulDifference R f d) 0
    (HomologicalComplex.homotopyCofiber.d (pairKoszulDifference R f d) (-1) 0 x) =
      (pairKoszulDifference R f d).f 0
        (fstX (pairKoszulDifference R f d) (-1) 0 (by decide) x) +
      (pairKoszulProduct R f d).d (-1) 0
        (sndX (pairKoszulDifference R f d) (-1) x) at h
  rw [h, map_add, pairKoszulProductZero_difference, pairKoszulProduct_d_negOne]
  simp [pairTowerObstruction, pairCompletionZeroEquiv_fst, pairCompletionZeroEquiv_snd,
    sub_neg_eq_add, add_assoc]

/-- 具体的な二座標完備化の短複体と、交差境界を保持した行列モデルの同型。 -/
def pairCompletionShortComplexIso (f d : R) :
    (pairKoszulCompletionComplex R f d).sc 0 ≅ pairTowerShortComplex R f d :=
  (pairKoszulCompletionComplex R f d).isoSc' (-1) 0 1
    ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by decide))
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)) ≪≫
      ShortComplex.isoMk (pairCompletionNegEquiv R f d).toModuleIso
        (pairCompletionZeroEquiv R f d).toModuleIso (pairCompletionOneEquiv R f d).toModuleIso
        (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
            exact (pairCompletion_d_neg R f d x).symm)
        (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
            exact (pairCompletion_d_zero R f d x).symm)

/-- 元の二座標Koszul完備化の短複体から、行列モデルへの同型。 -/
def pairKoszulCompletionShortComplexIso (f d : R) :
    (koszulCompletionComplex R (pairKoszulCoordinates R f d)).sc 0 ≅
      pairTowerShortComplex R f d :=
  (HomologicalComplex.shortComplexFunctor _ _ 0).mapIso (pairKoszulCompletionIso R f d) ≪≫
    pairCompletionShortComplexIso R f d

/-- 元の二座標Koszul完備化の実際のH⁰から、行列モデルのH⁰への同型。 -/
def pairKoszulCompletionH0Equiv (f d : R) :
    (koszulCompletionComplex R (pairKoszulCoordinates R f d)).homology 0 ≃ₗ[R]
      (pairTowerShortComplex R f d).homology :=
  (ShortComplex.homologyMapIso (pairKoszulCompletionShortComplexIso R f d)).toLinearEquiv

end SerrePositivity.DerivedCompletion

end PairKoszulConePart

section PairKoszulUnitPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 具体的な有限段への標準包含。 -/
def pairKoszulStageInclusion (f d : R) (n : ℕ) :
    principalSingle R ⟶ pairKoszulTower R f d n :=
  koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n) ≫
    CochainComplex.mappingCone.inr (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n))

/-- 有限段の表示同型は標準包含を保つ。 -/
theorem pairKoszulStageInclusion_naturality (f d : R) (n : ℕ) :
    koszulComplexInclusion R (fun i ↦ pairKoszulCoordinates R f d i ^ n) ≫
      (pairKoszulStageIso R f d n).hom = pairKoszulStageInclusion R f d n := by
  simp only [pairKoszulStageIso, pairKoszulTower, powerKoszulTower, koszulComplex_succ,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  simp only [pairKoszulStageInclusion, koszulComplexInclusion, pairKoszulCoordinates]
  rfl

/-- 具体的な有限段の零次数成分は、標準包含の元を保つ。 -/
theorem pairKoszulStageInclusion_zero (f d : R) (n : ℕ) (r : R) :
    pairKoszulStageZeroEquiv R f d n ((pairKoszulStageInclusion R f d n).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = r := by
  rw [pairKoszulStageZeroEquiv_apply]
  change (principalKoszulStageZeroIso R f n).hom
    (sndX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) 0
      (inrX (smulId (d ^ n) (powerKoszulTower R (fun _ : Fin 1 ↦ f) n)) 0
        ((koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n)).f 0
          ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)))) = r
  rw [moduleCone_snd_inr_apply]
  exact congrArg (fun g ↦ g.hom r) (principalKoszulInclusion_zero R f n)

/-- 元の標準写像を、具体的な塔表示へ運ぶ。 -/
def pairKoszulCompletionUnit (f d : R) :
    principalSingle R ⟶ pairKoszulCompletionComplex R f d :=
  koszulCompletionUnit R (pairKoszulCoordinates R f d) ≫ (pairKoszulCompletionIso R f d).hom

/-- 運んだ標準写像の第1射影を、各段の標準包含で計算する。 -/
theorem pairKoszulCompletionUnit_fst_projection (f d : R) (n : ℕ) :
    (pairKoszulCompletionUnit R f d).f 0 ≫ fstX (pairKoszulDifference R f d) (-1) 0 (by decide) ≫
      (Pi.π (pairKoszulTower R f d) n).f 0 = (pairKoszulStageInclusion R f d n).f 0 := by
  have he := complexTowerHomotopyLimitIso_fst_zero R
    (powerKoszulTransition R (pairKoszulCoordinates R f d)) (pairKoszulTransition R f d)
    (pairKoszulStageIso R f d) (fun n ↦ (pairKoszulStageIso_naturality R f d n).symm)
  change (pairKoszulCompletionIso R f d).hom.f 0 ≫
    fstX (pairKoszulDifference R f d) (-1) 0 (by decide) =
      fstX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
        (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1) 0 (by decide) ≫
      (complexTowerProductIso R (pairKoszulStageIso R f d)).hom.f 0 at he
  have hp := congrArg (fun g ↦ g.f 0)
    (complexTowerProductMap_projection R (fun n ↦ (pairKoszulStageIso R f d n).hom) n)
  have hu := congrArg (fun g ↦ g.f 0)
    (koszulCompletionUnit_comp_projection R (pairKoszulCoordinates R f d) n)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    complexTowerProjection_fst_zero] at hu
  change (koszulCompletionUnit R (pairKoszulCoordinates R f d)).f 0 ≫
    fstX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
      (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1) 0 (by decide) ≫
    (Pi.π (powerKoszulTower R (pairKoszulCoordinates R f d)) n).f 0 =
      (koszulComplexInclusion R (fun i ↦ pairKoszulCoordinates R f d i ^ n)).f 0 at hu
  have hi := congrArg (fun g ↦ g.f 0) (pairKoszulStageInclusion_naturality R f d n)
  change (koszulComplexInclusion R (fun i ↦ pairKoszulCoordinates R f d i ^ n)).f 0 ≫
    (pairKoszulStageIso R f d n).hom.f 0 = (pairKoszulStageInclusion R f d n).f 0 at hi
  let u := (koszulCompletionUnit R (pairKoszulCoordinates R f d)).f 0
  let F := fstX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
    (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1) 0 (by decide)
  let G := fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
  let a := (complexTowerProductIso R (pairKoszulStageIso R f d)).hom.f 0
  let pK := (Pi.π (powerKoszulTower R (pairKoszulCoordinates R f d)) n).f 0
  let pL := (Pi.π (pairKoszulTower R f d) n).f 0
  let q := (pairKoszulStageIso R f d n).hom.f 0
  have hp' : a ≫ pL = pK ≫ q := hp
  change u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G ≫ pL = _
  calc
    u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G ≫ pL =
        u ≫ ((pairKoszulCompletionIso R f d).hom.f 0 ≫ G) ≫ pL := by
          simp only [Category.assoc]
    _ = u ≫ (F ≫ a) ≫ pL := by rw [he]
    _ = (u ≫ F ≫ pK) ≫ q := by
      simp only [Category.assoc]
      rw [hp']
    _ = (pairKoszulStageInclusion R f d n).f 0 := by rw [hu, hi]

/-- 表示同型を通して運んだ標準写像の第2成分は零。 -/
theorem pairKoszulCompletionUnit_snd_zero (f d : R) :
    (pairKoszulCompletionUnit R f d).f 0 ≫ sndX (pairKoszulDifference R f d) (-1) = 0 := by
  have he := complexTowerHomotopyLimitIso_snd_zero R
    (powerKoszulTransition R (pairKoszulCoordinates R f d)) (pairKoszulTransition R f d)
    (pairKoszulStageIso R f d) (fun n ↦ (pairKoszulStageIso_naturality R f d n).symm)
  let u := (koszulCompletionUnit R (pairKoszulCoordinates R f d)).f 0
  let F := sndX (complexTowerDifference R (powerKoszulTower R (pairKoszulCoordinates R f d))
    (powerKoszulTransition R (pairKoszulCoordinates R f d))) (-1)
  let G := sndX (pairKoszulDifference R f d) (-1)
  let a := (complexTowerProductIso R (pairKoszulStageIso R f d)).hom.f (-1)
  have hu : u ≫ F = 0 := by
    dsimp only [u, F, koszulCompletionUnit, complexTowerCompatibleLift]
    apply complexTowerHomotopyLimitLift_snd_component
  change u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G = 0
  change (pairKoszulCompletionIso R f d).hom.f 0 ≫ G = F ≫ a at he
  calc
    u ≫ (pairKoszulCompletionIso R f d).hom.f 0 ≫ G =
        u ≫ ((pairKoszulCompletionIso R f d).hom.f 0 ≫ G) := rfl
    _ = (u ≫ F) ≫ a := by rw [he]; simp only [Category.assoc]
    _ = 0 := by rw [hu, CategoryTheory.Limits.zero_comp]

/-- 標準写像の第一列は定数列。 -/
theorem pairCompletionZeroEquiv_unit_fst (f d r : R) :
    (pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).1 = fun _ ↦ r := by
  funext n
  rw [pairCompletionZeroEquiv_fst, pairKoszulProductZeroEquiv_apply,
    complexProductDegreeEquiv_apply]
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))
      (pairKoszulCompletionUnit_fst_projection R f d n)
  change (Pi.π (pairKoszulTower R f d) n).f 0
    (fstX (pairKoszulDifference R f d) (-1) 0 (by decide)
      ((pairKoszulCompletionUnit R f d).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))) =
      (pairKoszulStageInclusion R f d n).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r) at h
  rw [h, pairKoszulStageInclusion_zero]

/-- 標準写像の二つの補助列は零。 -/
theorem pairCompletionZeroEquiv_unit_snd (f d r : R) :
    (pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).2 = 0 := by
  rw [pairCompletionZeroEquiv_snd]
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))
      (pairKoszulCompletionUnit_snd_zero R f d)
  change sndX (pairKoszulDifference R f d) (-1) ((pairKoszulCompletionUnit R f d).f 0
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = 0 at h
  rw [h, map_zero, neg_zero]

/-- 元の標準写像は、行列表示では定数列と二つの零列になる。 -/
theorem pairCompletionZeroEquiv_unit (f d r : R) :
    pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) =
      (fun _ ↦ r, (0, 0)) :=
  Prod.ext (pairCompletionZeroEquiv_unit_fst R f d r) (pairCompletionZeroEquiv_unit_snd R f d r)

/-- 元の標準写像を、行列モデルの短複体へ移した写像。 -/
def pairCompletionUnitShortMap (f d : R) :
    (principalSingle R).sc 0 ⟶ pairTowerShortComplex R f d :=
  (HomologicalComplex.shortComplexFunctor _ _ 0).map
    (koszulCompletionUnit R (pairKoszulCoordinates R f d)) ≫
      (pairKoszulCompletionShortComplexIso R f d).hom

/-- 標準短複体写像は、標準サイクルを保つ。 -/
theorem pairCompletionUnitShortMap_cycles (f d r : R) :
    ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d)
      ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r) =
      (pairTowerShortComplex R f d).moduleCatCyclesIso.inv
        (pairTowerConstantCycle R f d r) := by
  apply (ModuleCat.mono_iff_injective (pairTowerShortComplex R f d).iCycles).mp inferInstance
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r))
      (ShortComplex.cyclesMap_i (pairCompletionUnitShortMap R f d))
  change (pairTowerShortComplex R f d).iCycles
    (ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d)
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv r)) = (pairCompletionUnitShortMap R f d).τ₂
      ((principalSingle R).iCycles 0
        ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
          (ModuleCat.of R R)).inv r)) at h
  rw [h]
  have hsrc := congrArg (fun g ↦ g.hom r)
    (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles
      (ComplexShape.up ℤ) 0 (ModuleCat.of R R))
  change (principalSingle R).iCycles 0
    ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv r) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r at hsrc
  have htgt := congrArg (fun g ↦ g.hom (pairTowerConstantCycle R f d r))
    (pairTowerShortComplex R f d).moduleCatCyclesIso_inv_iCycles
  change (pairTowerShortComplex R f d).iCycles
    ((pairTowerShortComplex R f d).moduleCatCyclesIso.inv (pairTowerConstantCycle R f d r)) =
      (pairTowerConstantCycle R f d r).val at htgt
  rw [htgt]
  change (pairCompletionUnitShortMap R f d).τ₂
    ((principalSingle R).iCycles 0
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv r)) = _
  rw [hsrc]
  change pairCompletionZeroEquiv R f d ((pairKoszulCompletionUnit R f d).f 0
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [pairCompletionZeroEquiv_unit, pairTowerConstantCycle_val]

/-- 実際のH⁰の同型は、既存の標準写像をモデルの標準写像へ送る。 -/
theorem pairKoszulCompletionH0Equiv_unit (f d r : R) :
    pairKoszulCompletionH0Equiv R f d
      (koszulCompletionH0Unit R (pairKoszulCoordinates R f d) r) =
        pairTowerHomologyUnit R f d r := by
  let c : (principalSingle R).cycles 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r
  have hrep : (HomologicalComplex.singleObjHomologySelfIso _ 0 (ModuleCat.of R R)).inv r =
      (principalSingle R).homologyπ 0 c := by
    have h : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv ≫ (principalSingle R).homologyπ 0 := by
      rw [← HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact congrArg (fun g ↦ g.hom r) h
  have hn := congrArg (fun g ↦ g.hom c)
    (ShortComplex.homologyπ_naturality (pairCompletionUnitShortMap R f d))
  change ShortComplex.homologyMap (pairCompletionUnitShortMap R f d)
    ((principalSingle R).homologyπ 0 c) = (pairTowerShortComplex R f d).homologyπ
      (ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d) c) at hn
  rw [show ShortComplex.cyclesMap (pairCompletionUnitShortMap R f d) c =
    (pairTowerShortComplex R f d).moduleCatCyclesIso.inv (pairTowerConstantCycle R f d r)
      from pairCompletionUnitShortMap_cycles R f d r] at hn
  change ShortComplex.homologyMap (pairKoszulCompletionShortComplexIso R f d).hom
    (HomologicalComplex.homologyMap (koszulCompletionUnit R (pairKoszulCoordinates R f d)) 0
      ((HomologicalComplex.singleObjHomologySelfIso _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [hrep]
  have hcomp : ShortComplex.homologyMap (pairCompletionUnitShortMap R f d) =
      HomologicalComplex.homologyMap (koszulCompletionUnit R (pairKoszulCoordinates R f d)) 0 ≫
        ShortComplex.homologyMap (pairKoszulCompletionShortComplexIso R f d).hom :=
    ShortComplex.homologyMap_comp _ _
  rw [hcomp] at hn
  exact hn

end SerrePositivity.DerivedCompletion

end PairKoszulUnitPart

section PairKoszulRingPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 元の二座標Koszul塔の完備化の、実際の零次ホモロジー。 -/
abbrev PairCompletionH0 (f d : R) :=
  (koszulCompletionComplex R (pairKoszulCoordinates R f d)).homology 0

/-- 行列モデルのH⁰も、標準元について完備加群への反射となる。 -/
theorem pairTowerHomology_isCompleteModuleReflection (f d : R) :
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d)
      (pairTowerShortComplex R f d).homology (pairTowerHomologyUnit R f d 1) where
  isComplete j := isModuleComplete_of_linearEquiv R (pairKoszulCoordinates R f d j)
    (PairCompletionH0 R f d) (pairTowerShortComplex R f d).homology
      (pairKoszulCompletionH0Equiv R f d)
        (koszulCompletionH0_isModuleComplete R (pairKoszulCoordinates R f d) j)
  universal N hN := pairTowerHomology_evaluation_bijective R f d N
    (by simpa only [pairKoszulCoordinates, Fin.snoc_apply_zero] using hN 0)
    (by simpa only [pairKoszulCoordinates, Fin.snoc_last] using hN (Fin.last 1))

/-- 元の実際のH⁰は、既存の標準元について完備加群への反射となる。 -/
theorem pairCompletionH0_isCompleteModuleReflection (f d : R) :
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d) (PairCompletionH0 R f d)
      (koszulCompletionH0Unit R (pairKoszulCoordinates R f d) 1) :=
  (pairTowerHomology_isCompleteModuleReflection R f d).of_linearEquiv R
    (pairKoszulCompletionH0Equiv R f d).symm (by
      apply (pairKoszulCompletionH0Equiv R f d).injective
      rw [LinearEquiv.apply_symm_apply, pairKoszulCompletionH0Equiv_unit])

/-- 元の加法群とR作用を保つ、実際の二座標H⁰の可換環構造。 -/
@[instance_reducible] def pairCompletionCommRing (f d : R) : CommRing (PairCompletionH0 R f d) :=
  (pairCompletionH0_isCompleteModuleReflection R f d).commRing

/-- 実際の二座標H⁰のR代数構造。 -/
@[instance_reducible] def pairCompletionAlgebra (f d : R) :
    letI := pairCompletionCommRing R f d; Algebra R (PairCompletionH0 R f d) :=
  (pairCompletionH0_isCompleteModuleReflection R f d).algebra

/-- 既存のH⁰標準写像を環準同型として実現する。 -/
def pairCompletionUnitRingHom (f d : R) :
    letI := pairCompletionCommRing R f d; R →+* PairCompletionH0 R f d :=
  (pairCompletionH0_isCompleteModuleReflection R f d).unitRingHom

/-- 環としての標準写像は、既存のKoszul完備化のH⁰標準写像と一致する。 -/
theorem pairCompletionUnitRingHom_apply (f d r : R) :
    pairCompletionUnitRingHom R f d r = koszulCompletionH0Unit R (pairKoszulCoordinates R f d) r :=
  (pairCompletionH0_isCompleteModuleReflection R f d).unitRingHom_eq_linearMap
    (koszulCompletionH0Unit R (pairKoszulCoordinates R f d)) rfl r

/-- 実際の二座標H⁰は、最初の元fについて導来完備。 -/
theorem pairCompletionH0_isModuleComplete_first (f d : R) :
    IsModuleComplete R f (PairCompletionH0 R f d) := by
  simpa only [pairKoszulCoordinates, Fin.snoc_apply_zero] using
    (pairCompletionH0_isCompleteModuleReflection R f d).isComplete 0

/-- 実際の二座標H⁰は、二つ目の元dについて導来完備。 -/
theorem pairCompletionH0_isModuleComplete_second (f d : R) :
    IsModuleComplete R d (PairCompletionH0 R f d) := by
  simpa only [pairKoszulCoordinates, Fin.snoc_last] using
    (pairCompletionH0_isCompleteModuleReflection R f d).isComplete (Fin.last 1)

/-- 構成した代数の標準写像は、既存の標準環準同型と一致する。 -/
theorem pairCompletion_algebraMap (f d r : R) :
    letI := pairCompletionCommRing R f d
    letI := pairCompletionAlgebra R f d
    algebraMap R (PairCompletionH0 R f d) r = pairCompletionUnitRingHom R f d r := rfl

/-- 構成した代数構造は、標準環準同型から得る構造に一致する。 -/
theorem pairCompletionAlgebra_eq_toAlgebra (f d : R) :
    letI := pairCompletionCommRing R f d
    pairCompletionAlgebra R f d = (pairCompletionUnitRingHom R f d).toAlgebra := by
  let := pairCompletionCommRing R f d
  exact Algebra.algebra_ext _ _ (fun r ↦ pairCompletion_algebraMap R f d r)

/-- 標準環準同型による作用の下で、fについて導来完備。 -/
theorem pairCompletion_isModuleComplete_unit_first (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := (pairCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R f
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ inferInstance)) := by
  let := pairCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (PairCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R f
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ a)))
      (pairCompletionAlgebra_eq_toAlgebra R f d)) (pairCompletionH0_isModuleComplete_first R f d)

/-- 標準環準同型による作用の下で、dについて導来完備。 -/
theorem pairCompletion_isModuleComplete_unit_second (f d : R) :
    letI := pairCompletionCommRing R f d
    letI := (pairCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R d
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ inferInstance)) := by
  let := pairCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (PairCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R d
      (@ModuleCat.of R _ (PairCompletionH0 R f d) _
        (@Algebra.toModule R (PairCompletionH0 R f d) _ _ a)))
      (pairCompletionAlgebra_eq_toAlgebra R f d)) (pairCompletionH0_isModuleComplete_second R f d)

/-- 両座標の完備性を、列の各座標についての条件へ戻す。 -/
theorem pairKoszulCoordinates_isModuleComplete (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) :
    ∀ j, IsModuleComplete R (pairKoszulCoordinates R f d j) N := by
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [pairKoszulCoordinates, Fin.snoc_last] using hd
  · simpa only [pairKoszulCoordinates, Fin.snoc_castSucc] using hf

/-- 実際の二座標H⁰から、両座標で完備なR代数への延長は一意。 -/
theorem pairCompletion_existsUnique_algHom (f d : R)
    (T : Type u) [CommRing T] [Algebra R T]
    (hf : IsModuleComplete R f (ModuleCat.of R T))
    (hd : IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    letI := pairCompletionAlgebra R f d
    ∃! _g : PairCompletionH0 R f d →ₐ[R] T, True :=
  (pairCompletionH0_isCompleteModuleReflection R f d).existsUnique_algHom T
    (pairKoszulCoordinates_isModuleComplete R f d (ModuleCat.of R T) hf hd)

/-- 両方の座標について導来完備な離散 `R` 代数への代数写像の延長（`pairCompletion_existsUnique_algHom` の写像）。 -/
def pairCompletionLiftAlgHom (f d : R) (T : Type u) [CommRing T] [Algebra R T]
    (hf : IsModuleComplete R f (ModuleCat.of R T))
    (hd : IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    letI := pairCompletionAlgebra R f d
    PairCompletionH0 R f d →ₐ[R] T :=
  (pairCompletionH0_isCompleteModuleReflection R f d).liftAlgHom T
    (pairKoszulCoordinates_isModuleComplete R f d (ModuleCat.of R T) hf hd)

/-- 任意の環準同型は、実際の二座標H⁰の標準写像から一意に延長する。 -/
theorem pairCompletion_existsUnique_ringHom (f d : R)
    (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    ∃! h : PairCompletionH0 R f d →+* T, h.comp (pairCompletionUnitRingHom R f d) = g := by
  let := g.toAlgebra
  let := pairCompletionCommRing R f d
  let := pairCompletionAlgebra R f d
  obtain ⟨h, _, hu⟩ := pairCompletion_existsUnique_algHom R f d T hf hd
  refine ⟨h.toRingHom, ?_, ?_⟩
  · ext r
    exact h.commutes r
  · intro k hk
    let k' : PairCompletionH0 R f d →ₐ[R] T :=
      { k with commutes' := fun r ↦ congrArg (fun m : R →+* T ↦ m r) hk }
    exact congrArg AlgHom.toRingHom (hu k' trivial)

/-- 標準写像に沿った、両方の座標で導来完備な離散環への環準同型の延長
（`pairCompletion_existsUnique_ringHom` の写像）。 -/
def pairCompletionLift (f d : R) (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    PairCompletionH0 R f d →+* T := by
  letI := g.toAlgebra
  letI := pairCompletionCommRing R f d
  letI := pairCompletionAlgebra R f d
  exact (pairCompletionLiftAlgHom R f d T hf hd).toRingHom

/-- 延長は標準写像との合成で元の環準同型に戻る。 -/
theorem pairCompletionLift_comp (f d : R) (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pairCompletionCommRing R f d
    (pairCompletionLift R f d T g hf hd).comp (pairCompletionUnitRingHom R f d) = g := by
  letI := g.toAlgebra
  letI := pairCompletionCommRing R f d
  letI := pairCompletionAlgebra R f d
  ext r
  exact (pairCompletionLiftAlgHom R f d T hf hd).commutes r

end SerrePositivity.DerivedCompletion

end PairKoszulRingPart
