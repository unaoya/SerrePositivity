module

public import SerrePositivity.CommutativeAlgebra.ParameterGeneratorSequence

/-! # 最後のパラメータの正の冪への置換

パラメータの根基を保ち、最後の元を前の列と固定した正則元のイデアルへ入れる。
長さ・重複度の倍率の公式はこのモジュールの結論に含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open IsLocalRing
variable {R : Type u} [CommRing R]

/-- 列の最後だけを正の冪にしても、その生成イデアルの根基は変わらない。 -/
theorem radical_span_snoc_pow {r : ℕ} (y : Fin r → R) (a : R) (k : ℕ) (hk : 0 < k) :
    (Ideal.span (Set.range (Fin.snoc y (a ^ k)))).radical =
      (Ideal.span (Set.range (Fin.snoc y a))).radical := by
  simp only [Fin.range_snoc, Ideal.span_insert]
  rw [← Ideal.span_singleton_pow]
  calc
    _ = (((Ideal.span {a}) ^ k).radical ⊔ (Ideal.span (Set.range y)).radical).radical :=
      Ideal.radical_sup _ _
    _ = ((Ideal.span {a}).radical ⊔ (Ideal.span (Set.range y)).radical).radical := by
      rw [Ideal.radical_pow _ (Nat.ne_of_gt hk)]
    _ = _ := (Ideal.radical_sup _ _).symm

/-- 最後の生成元を正の冪にしたイデアルは、元の生成イデアルに含まれる。
パラメータ条件や局所性・Noether 性は不要。 -/
theorem span_snoc_pow_le {D : Type u} [CommRing D] {e : ℕ}
    (y : Fin e → D) (a : D) (k : ℕ) (hk : 0 < k) :
    Ideal.span (Set.range (Fin.snoc y (a ^ k))) ≤ Ideal.span (Set.range (Fin.snoc y a)) := by
  simp only [Fin.range_snoc, Ideal.span_insert]
  rw [← Ideal.span_singleton_pow]
  exact sup_le_sup (Ideal.pow_le_self (Nat.ne_of_gt hk)) le_rfl

/-- 列の最後を正の冪にする操作は、その生成イデアルを小さくする。 -/
theorem span_last_pow_le {D : Type u} [CommRing D] {e : ℕ}
    (z : Fin (e + 1) → D) (k : ℕ) (hk : 0 < k) :
    Ideal.span (Set.range (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k))) ≤
      Ideal.span (Set.range z) := by
  simpa only [Fin.snoc_init_self] using span_snoc_pow_le (Fin.init z) (z (Fin.last e)) k hk

/-- パラメータ系の最後だけを正の冪にしてもパラメータ系となる。 -/
theorem IsSystemOfParameters.pow_last [IsLocalRing R] {r : ℕ} {y : Fin (r + 1) → R}
    (hy : IsSystemOfParameters R y) (k : ℕ) (hk : 0 < k) :
    IsSystemOfParameters R (Fin.snoc (Fin.init y) (y (Fin.last r) ^ k)) := by
  refine ⟨hy.1, ?_⟩
  rw [radical_span_snoc_pow _ _ k hk, Fin.snoc_init_self]
  exact hy.2

/-- 元の生成イデアルを保つ列の変更と、最後の元の正の冪の所属を同時に得る。 -/
theorem exists_same_span_parameters_with_last_pow_mem
    [IsLocalRing R] [IsNoetherianRing R] {r : ℕ}
    (y : Fin (r + 1) → R) (hy : IsSystemOfParameters R y)
    (g : R) (hgm : g ∈ maximalIdeal R) (hg : IsSMulRegular R g) :
    ∃ (y' : Fin (r + 1) → R) (k : ℕ),
      Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
      IsSystemOfParameters R (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
      y' (Fin.last r) ^ k ∈ Ideal.span (Set.range (Fin.init y')) ⊔ Ideal.span {g} := by
  obtain ⟨y', hspan, hparam⟩ :=
    ParameterGeneratorSequence.exists_same_span_with_regular_last y hy g hgm hg
  have hy' : IsSystemOfParameters R y' := ⟨hy.1, by rw [hspan]; exact hy.2⟩
  have hlast : y' (Fin.last r) ∈ maximalIdeal R := by
    rw [← hy'.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self _))
  have hrad : (Ideal.span (Set.range (Fin.init y')) ⊔ Ideal.span {g}).radical = maximalIdeal R := by
    simpa only [Fin.range_snoc, Ideal.span_insert, sup_comm] using hparam.2
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp (hrad.symm ▸ hlast)
  refine ⟨y', k + 1, hspan, by omega, hy'.pow_last (k + 1) (by omega), ?_⟩
  rw [pow_succ]
  exact (Ideal.span (Set.range (Fin.init y')) ⊔ Ideal.span {g}).mul_mem_right _ hk

end SerrePositivity
