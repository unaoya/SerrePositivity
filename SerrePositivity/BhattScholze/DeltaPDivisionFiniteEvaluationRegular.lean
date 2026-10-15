module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceGraphKoszul
public import SerrePositivity.BhattScholze.DeltaPDivisionFiniteRelationsRegular

/-! # 実p除算の有限評価関係列のKoszul分解

全prefixのイデアル一致を使い、実反復差関係列から評価関係列へ正則性を移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

/-- 次段評価イデアルは、前段に次の評価関係を追加したもの。 -/
theorem deltaDivisionFiniteEvaluationIdeal_succ
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    deltaDivisionFiniteEvaluationIdeal D d a (N + 1) =
      deltaDivisionFiniteEvaluationIdeal D d a N ⊔
        Ideal.span (Set.range fun s => deltaDivisionEvaluationRelation D d a s (N + 1)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    by_cases hi : i.val < N + 1
    · apply (show deltaDivisionFiniteEvaluationIdeal D d a N ≤
        deltaDivisionFiniteEvaluationIdeal D d a N ⊔ _ from le_sup_left)
      exact Ideal.subset_span ⟨(s, ⟨i.val, hi⟩), rfl⟩
    · have he : i.val = N + 1 := by omega
      change deltaDivisionEvaluationRelation D d a s i.val ∈ _
      rw [he]
      exact (show Ideal.span (Set.range fun t => deltaDivisionEvaluationRelation D d a t (N + 1)) ≤
        deltaDivisionFiniteEvaluationIdeal D d a N ⊔ _ from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self s))
  · apply sup_le
    · rw [deltaDivisionFiniteEvaluationIdeal_eq, deltaDivisionFiniteEvaluationIdeal_eq]
      exact deltaDivisionFiniteRelationIdeal_mono D d a (Nat.le_succ N)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span ⟨(s, ⟨N + 1, Nat.lt_succ_self _⟩), rfl⟩

variable [Unique σ] (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 一元評価関係の全有限prefixの生成イデアルは既存の実I_N。 -/
theorem deltaPDivisionFiniteEvaluation_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) = I₀ N := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  unfold Ideal.ofList deltaDivisionFiniteEvaluationIdeal
  congr 1
  ext z
  simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, rfl⟩

/-- 前段商での次の反復差関係の非零因子性は、次の評価関係へ移る。 -/
theorem deltaPDivisionFiniteEvaluation_next_isSMulRegular (N : ℕ)
    (hg : IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1)))) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (h₀ (N + 1))) := by
  let q := Ideal.Quotient.mk (I₀ N)
  have he : I₀ (N + 1) = I₀ N ⊔ Ideal.span {h₀ (N + 1)} := by
    rw [← deltaDivisionFiniteEvaluationIdeal_eq D (p : A) a₀ (N + 1),
      deltaDivisionFiniteEvaluationIdeal_succ, deltaDivisionFiniteEvaluationIdeal_eq]
    congr 1
    congr 1
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s = (default : σ) := Subsingleton.elim _ _
      subst s
      exact Set.mem_singleton _
    · intro hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨default, rfl⟩
  have hm : g₀ (N + 1) ∈ I₀ N ⊔ Ideal.span {h₀ (N + 1)} := by
    rw [← he]
    exact Ideal.subset_span ⟨(default, ⟨N + 1, Nat.lt_succ_self _⟩), rfl⟩
  obtain ⟨r, hr, t, ht, hrt⟩ := Submodule.mem_sup.mp hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ht
  have hdiv : q (g₀ (N + 1)) = q (h₀ (N + 1)) * q b := by
    rw [← hrt, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_add, hb, map_mul]
  intro x z hxz
  apply hg
  change q (g₀ (N + 1)) * x = q (g₀ (N + 1)) * z
  change q (h₀ (N + 1)) * x = q (h₀ (N + 1)) * z at hxz
  calc
    q (g₀ (N + 1)) * x = q b * (q (h₀ (N + 1)) * x) := by rw [hdiv]; ring
    _ = q b * (q (h₀ (N + 1)) * z) := congrArg (fun w => q b * w) hxz
    _ = q (g₀ (N + 1)) * z := by rw [hdiv]; ring

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
