module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionFiniteNormalizedPresentation

/-! # 有限正規化関係イデアルの後続式 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 既存の有限正規化生成元は、次段への標準包含に整合する。 -/
theorem deltaDivisionFiniteNormalizedGenerator_castSucc (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (z : σ × Fin N) :
    relativeFreeFiniteStepInclusion N σ (deltaDivisionFiniteNormalizedGenerator D d a u N z) =
      deltaDivisionFiniteNormalizedGenerator D d a u (N + 1) (z.1, z.2.castSucc) := by
  unfold relativeFreeFiniteStepInclusion deltaDivisionFiniteNormalizedGenerator
  change MvPolynomial.rename _ (MvPolynomial.rename _ _) = MvPolynomial.rename _ _
  rw [MvPolynomial.rename_rename]
  rfl

/-- 次段の最上段生成元は、第Nモニック有限関係式そのもの。 -/
theorem deltaDivisionFiniteNormalizedGenerator_last (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (s : σ) :
    deltaDivisionFiniteNormalizedGenerator D d a u (N + 1) (s, Fin.last N) =
      deltaDivisionWittNormalizedPolynomial D d a u s N := by
  unfold deltaDivisionFiniteNormalizedGenerator
  change MvPolynomial.rename (fun w : σ × Fin (N + 2) => (w.1, w.2)) _ = _
  exact MvPolynomial.rename_id_apply _

/-- 有限正規化生成元族のspanの次段は、前段の像と最上段関係式族の和。 -/
theorem deltaDivisionFiniteNormalizedGenerators_span_succ (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u (N + 1))) =
      Ideal.map (relativeFreeFiniteStepInclusion N σ)
        (Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N))) ⊔
      Ideal.span (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    by_cases hi : i.val < N
    · let j : Fin N := ⟨i.val, hi⟩
      have he : j.castSucc = i := Fin.ext rfl
      rw [← he, ← deltaDivisionFiniteNormalizedGenerator_castSucc D d a u N (s, j)]
      apply (show Ideal.map (relativeFreeFiniteStepInclusion N σ)
          (Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N))) ≤
        _ from le_sup_left)
      apply Ideal.mem_map_of_mem
      exact Ideal.subset_span (Set.mem_range_self (s, j))
    · have he : i = Fin.last N := Fin.ext (by simp; omega)
      rw [he, deltaDivisionFiniteNormalizedGenerator_last]
      apply (show Ideal.span
          (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) ≤
        _ from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
  · apply sup_le
    · rw [Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      rw [deltaDivisionFiniteNormalizedGenerator_castSucc]
      exact Ideal.subset_span (Set.mem_range_self (z.1, z.2.castSucc))
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      change deltaDivisionWittNormalizedPolynomial D d a u s N ∈ _
      rw [← deltaDivisionFiniteNormalizedGenerator_last D d a u N s]
      exact Ideal.subset_span (Set.mem_range_self (s, Fin.last N))

/-- 有限正規化イデアルの次段は、前段の包含像にモニック関係式族を加えたもの。 -/
theorem deltaDivisionFiniteNormalizedPresentationIdeal_succ (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    deltaDivisionFiniteNormalizedPresentationIdeal D d a u (N + 1) =
      Ideal.map (relativeFreeFiniteStepInclusion N σ)
        (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ⊔
      Ideal.span (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) := by
  let q := relativeFreeFiniteStepInclusion (A := A) N σ
  have hC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [q, relativeFreeFiniteStepInclusion]
  have hX (s : σ) : q (MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1)))) =
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 2))) := by
    simp [q, relativeFreeFiniteStepInclusion]
  have hA : q '' (Set.range fun s => MvPolynomial.C (a s)) =
      Set.range fun s => MvPolynomial.C (a s) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hC _).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hC _⟩
  have hroot (s : σ) : q (MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 2))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    rw [map_sub, map_pow, hX, hC]
  have hR : q '' (Set.range fun s =>
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      Set.range fun s => MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 2))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hroot s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hroot s⟩
  change deltaDivisionFiniteNormalizedPresentationIdeal D d a u (N + 1) =
    Ideal.map q (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ⊔ _
  have hG := deltaDivisionFiniteNormalizedGenerators_span_succ D d a u N
  unfold deltaDivisionFiniteNormalizedPresentationIdeal
  rw [hG]
  simp only [Ideal.map_sup]
  simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_natCast, hC, hA, hR]
  exact (sup_assoc _ _ _).symm

/-- 最高変数分離後の次段イデアルは、前段係数イデアルとモニック冪族の和。 -/
theorem deltaDivisionFiniteNormalizedPresentationIdeal_map_top_split
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.map (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a u (N + 1)) =
      Ideal.map MvPolynomial.C (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ⊔
      Ideal.span (Set.range fun s => MvPolynomial.X s ^ p -
        MvPolynomial.C (deltaDivisionWittNormalizedCoefficient D d a u s N)) := by
  let f := (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom
  have hc : f.comp (relativeFreeFiniteStepInclusion N σ) = MvPolynomial.C := by
    apply RingHom.ext
    intro b
    exact relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion N σ A b
  have hs : f '' (Set.range fun s => deltaDivisionWittNormalizedPolynomial D d a u s N) =
      Set.range (fun s => MvPolynomial.X s ^ p -
        MvPolynomial.C (deltaDivisionWittNormalizedCoefficient D d a u s N)) := by
    ext b
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (deltaDivisionWittNormalizedPolynomial_top_split D d a u s N).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, deltaDivisionWittNormalizedPolynomial_top_split D d a u s N⟩
  change Ideal.map f _ = _
  rw [deltaDivisionFiniteNormalizedPresentationIdeal_succ, Ideal.map_sup,
    Ideal.map_map, hc, Ideal.map_span, hs]

end SerrePositivity.BhattScholze
