module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteEvaluationRegular
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionFiniteRelationsRegular

/-! # 実p除算の有限評価関係列のKoszul分解

全prefixのイデアル一致を使い、実反復差関係列から評価関係列へ正則性を移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

variable [Unique σ] (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 一元評価関係の全有限prefixの生成イデアルは既存の実I_N。 -/
theorem deltaPDivisionFiniteEvaluation_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) = I₀ N := by
  exact deltaDivisionFiniteEvaluation_ofList D (p : A) a₀ N

/-- 前段商での次の反復差関係の非零因子性は、次の評価関係へ移る。 -/
theorem deltaPDivisionFiniteEvaluation_next_isSMulRegular (N : ℕ)
    (hg : IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1)))) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (h₀ (N + 1))) := by
  exact deltaDivisionFiniteEvaluation_next_isSMulRegular D (p : A) a₀ N hg

/-- 正則一元入力では、実評価関係の全有限列が弱正則。 -/
theorem deltaPDivisionFiniteEvaluation_isWeaklyRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular L₀ (List.ofFn fun i : Fin (N + 1) => h₀ i.val) := by
  induction N with
  | zero =>
      have hr := deltaPDivisionFirstRelation_isSMulRegular (σ := σ) D y hpA
      rw [List.ofFn_succ, List.ofFn_zero,
        RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      intro x z hxz
      apply hr
      change (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
        MvPolynomial.C (D.frobeniusLift y)) * x =
          (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
            MvPolynomial.C (D.frobeniusLift y)) * z
      change (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
        MvPolynomial.C (D.frobeniusLift y)) * x =
          (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) -
            MvPolynomial.C (D.frobeniusLift y)) * z at hxz
      exact hxz
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) • ⊤ :
          Submodule L₀ L₀) = I₀ N := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaPDivisionFiniteEvaluation_ofList]
      change IsSMulRegular (L₀ ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) • ⊤ : Submodule L₀ L₀))
        (h₀ (N + 1))
      rw [hI]
      exact (isSMulRegular_map (Ideal.Quotient.mk (I₀ N)) (fun _ => rfl)).mp
        (deltaPDivisionFiniteEvaluation_next_isSMulRegular D y N
          (deltaPDivisionFiniteStage_next_isSMulRegular D y hpA hg v hv hy N))

/-- 実評価関係の有限Koszul複体は、実際の有限通常商を分解する。 -/
theorem deltaPDivisionFiniteEvaluation_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => h₀ i.val) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaPDivisionFiniteEvaluation_isWeaklyRegular D y hpA hg v hv hy N)

end SerrePositivity.BhattScholze
