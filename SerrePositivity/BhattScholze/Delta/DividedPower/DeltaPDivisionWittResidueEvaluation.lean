module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionWittResidueSolution
public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeWittCoefficientNaturality
public import SerrePositivity.BhattScholze.Delta.Free.Finite.DeltaWittJetComparison
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionIteratedRelations
public import Mathlib.RingTheory.Regular.Flat

/-! # 具体的Witt解を用いるrawδ除算包からの通常環射

全Witt係数の消滅を既存jet比較で全δ関係の消滅へ移す。
終域のδ構造・p正則性・完備性は要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B σ : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (q : A →+* B) (y : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => relativeFreeDeltaStructure σ D
local notation "a₀" => fun s ↦ D.frobeniusLift (y s)

/-- 逆Witt座標に具体的な除算解の全係数を代入する通常環射。 -/
def deltaPDivisionWittResidueEval : L₀ →+* B :=
  (MvPolynomial.eval₂Hom q (fun z : σ × ℕ ↦
    (deltaPDivisionWittResidueSolution D q (y z.1)).coeff z.2)).comp
      (relativeFreeWittInverseMap D hpA).toRingHom

/-- 通常評価は元の係数射を保つ。 -/
theorem deltaPDivisionWittResidueEval_C (r : A) :
    deltaPDivisionWittResidueEval D hpA q y (MvPolynomial.C r) = q r := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (MvPolynomial.C r)) = _
  rw [show relativeFreeWittInverseMap D hpA (MvPolynomial.C r) = MvPolynomial.C r from
    AlgHom.commutes (relativeFreeWittInverseMap D hpA) r, MvPolynomial.eval₂Hom_C]

/-- 各自由変数のWitt係数は具体的除算解の対応する係数に写る。 -/
theorem deltaPDivisionWittResidueEval_coefficient (s : σ) (n : ℕ) :
    deltaPDivisionWittResidueEval D hpA q y (relativeFreeWittGhostCoefficient D s n) =
      (deltaPDivisionWittResidueSolution D q (y s)).coeff n := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (relativeFreeWittGhostCoefficient D s n)) = _
  rw [relativeFreeWittInverseMap_coefficient, MvPolynomial.eval₂Hom_X']

/-- 自由初期変数の全Witt元は具体的除算解そのものに写る。 -/
theorem deltaPDivisionWittResidueEval_witt_X (s : σ) :
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) =
        deltaPDivisionWittResidueSolution D q (y s) := by
  ext n
  rw [WittVector.map_coeff]
  exact deltaPDivisionWittResidueEval_coefficient D hpA q y s n

/-- 基底係数の全Witt元は元の通常係数射の像に写る。 -/
theorem deltaPDivisionWittResidueEval_witt_C
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀)) (r : A) :
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C r)) =
        WittVector.map q (deltaWittGhostVector D r) := by
  ext n
  rw [WittVector.map_coeff, deltaWittGhostVector_relativeFree_C_coeff D hgL,
    deltaPDivisionWittResidueEval_C, WittVector.map_coeff]

/-- 実初期除算関係のWitt元はこの通常評価によって零になる。 -/
theorem deltaPDivisionWittResidueEval_kills_witt_relation
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (s : σ) :
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
        MvPolynomial.C (D.frobeniusLift (y s)))) = 0 := by
  change WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
    (deltaWittGhostRingHom F₀ hgL (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
      MvPolynomial.C (D.frobeniusLift (y s)))) = 0
  rw [map_sub, map_mul, map_sub, map_mul]
  change WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C (p : A))) *
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) -
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C (D.frobeniusLift (y s)))) = 0
  rw [deltaPDivisionWittResidueEval_witt_C D hpA q y hgL,
    deltaPDivisionWittResidueEval_witt_X, deltaPDivisionWittResidueEval_witt_C D hpA q y hgL]
  exact sub_eq_zero.mpr (deltaPDivisionWittResidueSolution_mul_source_prime D q (y s) hgA (hqy s))

/-- 実除算関係のすべてのδ反復像が、この通常評価で零になる。 -/
theorem deltaPDivisionWittResidueEval_kills_iterated_relation
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (s : σ) (n : ℕ) :
    deltaPDivisionWittResidueEval D hpA q y
      (deltaDivisionIteratedRelation D (p : A) a₀ s n) = 0 := by
  have hpL : Function.Injective (fun x : L₀ ↦ (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hw := deltaPDivisionWittResidueEval_kills_witt_relation D hpA q y hgA hgL hqy s
  have hc : ∀ i ≤ n, deltaPDivisionWittResidueEval D hpA q y
      ((deltaWittGhostVector F₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
        MvPolynomial.C (D.frobeniusLift (y s)))).coeff i) = 0 := by
    intro i _
    have h := congrArg (fun w : WittVector p B ↦ w.coeff i) hw
    simpa only [WittVector.map_coeff, WittVector.zero_coeff] using h
  have hj := (deltaWittGhostVector_jets_zero_iff F₀ hpL hgL
    (deltaPDivisionWittResidueEval D hpA q y)
    (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
      MvPolynomial.C (D.frobeniusLift (y s))) n).mpr hc
  exact hj n le_rfl

/-- 全δ関係を消す評価から得る、rawδ p除算包からの実通常環射。 -/
def deltaPDivisionWittResidueMap
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) : DeltaAdjoinDivision D (p : A) a₀ →+* B :=
  deltaDivisionIteratedRelationsLift D (p : A) a₀ (deltaPDivisionWittResidueEval D hpA q y)
    (deltaPDivisionWittResidueEval_kills_iterated_relation D hpA q y hgA hgL hqy)

/-- raw包からの実通常射は元の全自由環の評価を延長する。 -/
theorem deltaPDivisionWittResidueMap_comp_mk
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) :
    (deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy).comp
      (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal (p : A) a₀))) = deltaPDivisionWittResidueEval D hpA q y := rfl

/-- 実通常射は基底の係数射qを保つ。 -/
theorem deltaPDivisionWittResidueMap_coeff
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (r : A) :
    deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy
      (deltaAdjoinDivisionMap D (p : A) a₀ r) = q r :=
  deltaPDivisionWittResidueEval_C D hpA q y r

/-- 初期除算変数の像はq(δy_s)。 -/
theorem deltaPDivisionWittResidueMap_variable
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (s : σ) :
    deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy
      (deltaAdjoinDivisionVariable D (p : A) a₀ s) = q (D.delta (y s)) := by
  have h := deltaPDivisionWittResidueEval_coefficient D hpA q y s 0
  exact h.trans (deltaPDivisionWittResidueSolution_coeff_zero D q (y s) hpA)

/-- 元のAからの標準射と実通常射の合成はqそのもの。 -/
theorem deltaPDivisionWittResidueMap_comp_base
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) :
    (deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy).comp
      (deltaAdjoinDivisionMap D (p : A) a₀) = q := by
  ext r
  exact deltaPDivisionWittResidueMap_coeff D hpA q y hgA hgL hqy r

end SerrePositivity.BhattScholze
