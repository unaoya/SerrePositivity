module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteRelationsRegular
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionFiniteStageRegular

/-! # 実一元p除算関係の非零因子性

最高係数pの正則性と後続変数表示を用いる。mod pでの正則性だけからは結論しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 最初の実p除算関係は、Aのp正則性だけで自由δ環上の非零因子。 -/
theorem deltaPDivisionFirstRelation_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x)) :
    IsSMulRegular L₀ (g₀ 0) := by
  exact deltaDivisionFirstRelation_isSMulRegular D (p : A) a₀ (default : σ) hpA

/-- 前段実関係商がp正則なら、次の実p除算関係はその商上で非零因子。 -/
theorem deltaPDivisionFiniteStage_next_isSMulRegular_of_p_regular (N : ℕ)
    (hpQ : Function.Injective (fun x : L₀ ⧸ I₀ N => (p : _) * x)) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1))) := by
  apply deltaDivisionFiniteStage_next_isSMulRegular_of_frobenius_regular D (p : A) a₀ N
    (default : σ)
  have hφ : ∀ n : ℕ, D.frobeniusLift^[n] (p : A) = p := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_natCast]
  simpa only [hφ, map_natCast] using
    (show IsSMulRegular (L₀ ⧸ I₀ N) (p : L₀ ⧸ I₀ N) from hpQ)

/-- 正則な一元入力の全有限段で、次の実δ関係は通常商上の非零因子。
単元δ(p)とghost単射は既存p正則性の中間入力として保持する。 -/
theorem deltaPDivisionFiniteStage_next_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1))) :=
  deltaPDivisionFiniteStage_next_isSMulRegular_of_p_regular D y N
    (deltaPDivisionFiniteStage_quotient_p_mul_injective D y hpA hg v hv hy N)

/-- 全有限実関係列の生成イデアルは、既存の全有限段関係イデアル。 -/
theorem deltaPDivisionFiniteRelations_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) = I₀ N := by
  unfold Ideal.ofList deltaDivisionFiniteRelationIdeal
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

/-- pを前置しない実δ関係列自身の弱正則性。 -/
theorem deltaPDivisionFiniteRelations_isWeaklyRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular L₀ (List.ofFn fun i : Fin (N + 1) => g₀ i.val) := by
  induction N with
  | zero =>
      simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero] using
        (RingTheory.Sequence.isWeaklyRegular_singleton_iff L₀ (g₀ 0)).mpr
          (deltaPDivisionFirstRelation_isSMulRegular D y hpA)
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) • ⊤ :
          Submodule L₀ L₀) = I₀ N := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaPDivisionFiniteRelations_ofList]
      change IsSMulRegular (L₀ ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) • ⊤ : Submodule L₀ L₀))
        (g₀ (N + 1))
      rw [hI]
      exact (isSMulRegular_map (Ideal.Quotient.mk (I₀ N)) (fun _ => rfl)).mp
        (deltaPDivisionFiniteStage_next_isSMulRegular D y hpA hg v hv hy N)

/-- 実δ関係g₀,…,g_NのKoszul複体は、実際の有限通常商の分解。
André・perfectoid化全射性の引用には依存しない。 -/
theorem deltaPDivisionFiniteRelations_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => g₀ i.val) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaPDivisionFiniteRelations_isWeaklyRegular D y hpA hg v hv hy N)

end SerrePositivity.BhattScholze
