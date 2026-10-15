module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceGraphKoszul

/-! # 一般除数の有限反復δ関係と評価関係の正則性

全有限prefixの生成イデアルの一致を用いる。一元添字で任意除数・任意入力を扱い、
完備性・p正則性・ghost単射は要求しない。
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

variable [Unique σ] (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "g₀" => deltaDivisionIteratedRelation D d a (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation D d a (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- 一元評価関係の全有限prefixの生成イデアルは既存の実I_N。 -/
theorem deltaDivisionFiniteEvaluation_ofList (N : ℕ) :
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
theorem deltaDivisionFiniteEvaluation_next_isSMulRegular (N : ℕ)
    (hg : IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1)))) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (h₀ (N + 1))) := by
  let q := Ideal.Quotient.mk (I₀ N)
  have he : I₀ (N + 1) = I₀ N ⊔ Ideal.span {h₀ (N + 1)} := by
    rw [← deltaDivisionFiniteEvaluationIdeal_eq D d a (N + 1),
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

end SerrePositivity.BhattScholze
