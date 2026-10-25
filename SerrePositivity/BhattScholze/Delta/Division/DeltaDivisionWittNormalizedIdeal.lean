module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionWittNormalizedRelation
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionFirstResiduePresentation

/-! # 逆Witt座標による全有限関係イデアルの正規化

実際の有限δイデアルの全段式を、具体的モニック関係元族へ移す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期N段の正規化有限モニック関係式の包含像で生成したイデアル。 -/
def deltaDivisionFiniteNormalizedWittIdeal (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin N =>
    relativeFreeFiniteInitialPolynomialMap (z.2.val + 2) σ A
      (deltaDivisionWittNormalizedPolynomial D d a u z.1 z.2.val))

/-- 逆座標射による実際のWitt根関係イデアルの像は正規化モニックイデアル。 -/
theorem deltaDivisionFiniteWittRelationIdeal_inverse_map (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.map (relativeFreeWittInverseMap D hp).toRingHom
      (deltaDivisionFiniteWittRelationIdeal D d a u N) =
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  rw [deltaDivisionFiniteWittRelationIdeal, Ideal.map_span,
    deltaDivisionFiniteNormalizedWittIdeal]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (deltaDivisionRelativeWittRelationElement_inverse_image
      D hp hg d a u z.1 z.2.val).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, deltaDivisionRelativeWittRelationElement_inverse_image
      D hp hg d a u z.1 z.2.val⟩

/-- 逆Witt座標射は、既存第一剰余イデアルを固定する。 -/
theorem deltaDivisionFirstResidueIdeal_inverse_map (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    Ideal.map (relativeFreeWittInverseMap D hp).toRingHom
      (deltaDivisionFirstResidueIdeal D d a) = deltaDivisionFirstResidueIdeal D d a := by
  let q := (relativeFreeWittInverseMap (σ := σ) D hp).toRingHom
  have hC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b :=
    AlgHom.commutes (relativeFreeWittInverseMap D hp) b
  have hX (s : σ) : q (MvPolynomial.X (s, 0)) = MvPolynomial.X (s, 0) := by
    change relativeFreeWittInverseMap D hp (MvPolynomial.X (s, 0)) = _
    have h := relativeFreeWittInverseMap_coefficient D hp s 0
    simpa only [relativeFreeWittGhostCoefficient_zero] using h
  have hA : q '' (Set.range fun s => MvPolynomial.C (a s)) =
      Set.range fun s => MvPolynomial.C (a s) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hC _).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hC _⟩
  have hroot (s : σ) : q (MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      MvPolynomial.X (s, 0) ^ p - MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    rw [map_sub, map_pow, hX, hC]
  have hR : q '' (Set.range fun s => MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s))) =
      Set.range fun s => MvPolynomial.X (s, 0) ^ p -
        MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a s)) := by
    ext f
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hroot s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨s, rfl⟩, hroot s⟩
  rw [deltaDivisionFirstResidueIdeal_eq_monic D d a u hu]
  change Ideal.map q (deltaDivisionFirstMonicIdeal D d a u) = _
  simp only [deltaDivisionFirstMonicIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton, map_natCast, hC, hA, hR]

/-- 全有限δ剰余イデアルの逆座標像は、第一段の像と正規化モニックイデアルの和。 -/
theorem deltaDivisionFiniteRelationIdeal_inverse_map (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    Ideal.map (relativeFreeWittInverseMap D hpA).toRingHom
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        deltaDivisionFiniteRelationIdeal D d a (N + 1)) =
      Ideal.map (relativeFreeWittInverseMap D hpA).toRingHom
        (deltaDivisionFirstResidueIdeal D d a) ⊔
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  rw [deltaDivisionFiniteRelationIdeal_eq_first_sup_witt D d a u hu hpL hg,
    Ideal.map_sup, deltaDivisionFiniteWittRelationIdeal_inverse_map D hpA hg]

/-- 全有限δ剰余イデアルの逆座標像は、第一剰余と具体的モニック関係元族の和。 -/
theorem deltaDivisionFiniteRelationIdeal_inverse_map_eq_first_sup_normalized
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    Ideal.map (relativeFreeWittInverseMap D hpA).toRingHom
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        deltaDivisionFiniteRelationIdeal D d a (N + 1)) =
      deltaDivisionFirstResidueIdeal D d a ⊔
        deltaDivisionFiniteNormalizedWittIdeal D d a u N := by
  rw [deltaDivisionFiniteRelationIdeal_inverse_map D hpA hpL hg d a u hu,
    deltaDivisionFirstResidueIdeal_inverse_map D hpA d a u hu]

end SerrePositivity.BhattScholze
