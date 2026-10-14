module

public import SerrePositivity.BhattScholze.DeltaDivisionWittNormalizedQuotient

/-! # 正規化関係イデアルの初期有限変数による表示 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期N段の各モニック関係式を初期N+1変数の環に置いた生成元。 -/
def deltaDivisionFiniteNormalizedGenerator (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (z : σ × Fin N) :
    MvPolynomial (σ × Fin (N + 1)) A :=
  MvPolynomial.rename
    (fun w : σ × Fin (z.2.val + 2) => (w.1, (⟨w.2.val, by omega⟩ : Fin (N + 1))))
    (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val)

/-- 有限環に置いた生成元の包含像は元のモニック関係式の包含像。 -/
theorem deltaDivisionFiniteNormalizedGenerator_image (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (z : σ × Fin N) :
    relativeFreeFiniteInitialPolynomialMap (N + 1) σ A
      (deltaDivisionFiniteNormalizedGenerator D d a u N z) =
      relativeFreeFiniteInitialPolynomialMap (z.2.val + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val) := by
  unfold deltaDivisionFiniteNormalizedGenerator relativeFreeFiniteInitialPolynomialMap
  rw [MvPolynomial.rename_rename]
  rfl

/-- 第一段の係数・モニック関係と全初期N段の関係を有限環に置いたイデアル。 -/
def deltaDivisionFiniteNormalizedPresentationIdeal (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : Ideal (MvPolynomial (σ × Fin (N + 1)) A) :=
  ((Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A), MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s => MvPolynomial.C (a s))) ⊔
    Ideal.span (Set.range fun s => MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)))) ⊔
    Ideal.span (Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N))

/-- 有限表示イデアルの包含像は実際の正規化イデアルに一致する。 -/
theorem deltaDivisionFiniteNormalizedPresentationIdeal_map_initial (D : DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    Ideal.map (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) =
      deltaDivisionFirstResidueIdeal D d a ⊔
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  let q := (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
  have hC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [q, relativeFreeFiniteInitialPolynomialMap]
  have hX (s : σ) : q (MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1)))) =
      MvPolynomial.X (s, 0) := by
    simp [q, relativeFreeFiniteInitialPolynomialMap]
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
      MvPolynomial.X (s, 0) ^ p - MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    rw [map_sub, map_pow, hX, hC]
  have hR : q '' (Set.range fun s =>
      MvPolynomial.X (s, (⟨0, by omega⟩ : Fin (N + 1))) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      Set.range fun s => MvPolynomial.X (s, 0) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hroot s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hroot s⟩
  have hG : q '' Set.range (deltaDivisionFiniteNormalizedGenerator D d a u N) =
      Set.range (fun z : σ × Fin N => relativeFreeFiniteInitialPolynomialMap (z.2.val + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (deltaDivisionFiniteNormalizedGenerator_image D d a u N z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, deltaDivisionFiniteNormalizedGenerator_image D d a u N z⟩
  rw [deltaDivisionFirstResidueIdeal_eq_monic D d a u hu]
  change Ideal.map q _ = _
  simp only [deltaDivisionFiniteNormalizedPresentationIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton, map_natCast, hC, hA, hR, hG,
    deltaDivisionFirstMonicIdeal, deltaDivisionFiniteNormalizedWittIdeal]

end SerrePositivity.BhattScholze
