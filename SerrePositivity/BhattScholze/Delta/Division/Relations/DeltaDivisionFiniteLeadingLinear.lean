module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteRelationPolynomial

/-! # 実δ反復関係の整係数での最高変数分離

第n関係の最高変数は一次で係数φ^n(d)、残りは厳密に下のn段に属する。
p剰余への移行もpねじれの消去も使わない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem initial_delta_exists (D : DeltaStructure p A) (n : ℕ)
    (b : MvPolynomial (σ × Fin n) A) :
    ∃ c : MvPolynomial (σ × Fin (n + 1)) A,
      (relativeFreeDeltaStructure σ D).delta
        (relativeFreeFiniteInitialPolynomialMap n σ A b) =
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A c := by
  cases n with
  | zero =>
      let e := MvPolynomial.isEmptyAlgEquiv A (σ × Fin 0)
      have hb : b = MvPolynomial.C (e b) := by
        simpa only [e, MvPolynomial.isEmptyAlgEquiv_symm_apply] using (e.symm_apply_apply b).symm
      refine ⟨MvPolynomial.C (D.delta (e b)), ?_⟩
      conv_lhs => rw [hb]
      simp [relativeFreeFiniteInitialPolynomialMap]
  | succ n =>
      exact ⟨relativeFreeFiniteDeltaStep n σ D b,
        relativeFreeFiniteDeltaStep_delta_image n σ D b⟩

private theorem affine_delta_exists (D : DeltaStructure p A) (c : A) (s : σ) (n : ℕ)
    (b : MvPolynomial (σ × Fin n) A) :
    ∃ b' : MvPolynomial (σ × Fin (n + 1)) A,
      (relativeFreeDeltaStructure σ D).delta
        (MvPolynomial.C c * MvPolynomial.X (s, n) +
          relativeFreeFiniteInitialPolynomialMap n σ A b) =
        MvPolynomial.C (D.frobeniusLift c) * MvPolynomial.X (s, n + 1) +
          relativeFreeFiniteInitialPolynomialMap (n + 1) σ A b' := by
  let i := relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
  let b₀ := MvPolynomial.rename (fun z : σ × Fin n => (z.1, z.2.castSucc)) b
  let x : MvPolynomial (σ × Fin (n + 1)) A := MvPolynomial.X (s, Fin.last n)
  have hb₀ : i b₀ = relativeFreeFiniteInitialPolynomialMap n σ A b := by
    simp only [i, b₀, relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_rename,
      Function.comp_def, Fin.val_castSucc]
  have hx : i x = MvPolynomial.X (s, n) := by
    simp [i, x, relativeFreeFiniteInitialPolynomialMap]
  obtain ⟨g, hg⟩ := initial_delta_exists D n b
  let carry := (WittVector.teichmuller p (MvPolynomial.C c * x) +
    WittVector.teichmuller p b₀).coeff 1
  have hc : i carry = (WittVector.teichmuller p
      (MvPolynomial.C c * MvPolynomial.X (s, n)) +
      WittVector.teichmuller p (relativeFreeFiniteInitialPolynomialMap n σ A b)).coeff 1 := by
    change (WittVector.map i.toRingHom
      (WittVector.teichmuller p (MvPolynomial.C c * x) +
        WittVector.teichmuller p b₀)).coeff 1 = _
    rw [map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, hx, hb₀]
    simp only [i, relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_C]
  refine ⟨MvPolynomial.C (D.delta c) * x ^ p + g + carry, ?_⟩
  rw [DeltaStructure.delta_add, DeltaStructure.delta_mul,
    relativeFreeDeltaStructure_delta_C, relativeFreeDeltaStructure_delta_X, hg]
  change _ = _ + i (MvPolynomial.C (D.delta c) * x ^ p + g + carry)
  simp only [map_add, map_mul, map_pow, hx, hc]
  simp only [i, relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_C]
  rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
  ring

/-- 実関係式の第n変数は一次で係数φ^n(d)。残余は厳密に初期n段に属する。 -/
theorem exists_deltaDivisionFiniteLeadingLowerPolynomial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    ∃ b : MvPolynomial (σ × Fin n) A,
      deltaDivisionIteratedRelation D d a s n =
        MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, n) +
          relativeFreeFiniteInitialPolynomialMap n σ A b := by
  induction n with
  | zero =>
      refine ⟨-MvPolynomial.C (a s), ?_⟩
      simp [deltaDivisionIteratedRelation, relativeFreeFiniteInitialPolynomialMap, sub_eq_add_neg]
  | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨b', hb'⟩ := affine_delta_exists D (D.frobeniusLift^[n] d) s n b
      refine ⟨b', ?_⟩
      change (relativeFreeDeltaStructure σ D).delta^[n + 1] _ = _
      rw [Function.iterate_succ_apply']
      change (relativeFreeDeltaStructure σ D).delta
        (deltaDivisionIteratedRelation D d a s n) = _
      rw [hb, hb', Function.iterate_succ_apply']

/-- 最高変数を除いた、厳密に初期n段上の下位多項式。 -/
def deltaDivisionFiniteLeadingLowerPolynomial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    MvPolynomial (σ × Fin n) A :=
  Classical.choose (exists_deltaDivisionFiniteLeadingLowerPolynomial D d a s n)

/-- 選んだ下位多項式による整係数の最高変数分離の等式。 -/
theorem deltaDivisionIteratedRelation_eq_leading_add_lower
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionIteratedRelation D d a s n =
      MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, n) +
        relativeFreeFiniteInitialPolynomialMap n σ A
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s n) :=
  Classical.choose_spec (exists_deltaDivisionFiniteLeadingLowerPolynomial D d a s n)

/-- 下位多項式は厳密な初期段の単射性によって一意。 -/
theorem deltaDivisionFiniteLeadingLowerPolynomial_unique
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ)
    (b : MvPolynomial (σ × Fin n) A)
    (hb : deltaDivisionIteratedRelation D d a s n =
      MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, n) +
        relativeFreeFiniteInitialPolynomialMap n σ A b) :
    b = deltaDivisionFiniteLeadingLowerPolynomial D d a s n := by
  apply relativeFreeFiniteInitialPolynomialMap_injective n σ
  exact add_left_cancel (hb.symm.trans
    (deltaDivisionIteratedRelation_eq_leading_add_lower D d a s n))

/-- 有限関係式自体にも整係数の一次分離が成り立つ。 -/
theorem deltaDivisionFiniteRelationPolynomial_eq_leading_add_lower
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionFiniteRelationPolynomial D d a s n =
      MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, Fin.last n) +
        MvPolynomial.rename (fun z : σ × Fin n => (z.1, z.2.castSucc))
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s n) := by
  apply relativeFreeFiniteInitialPolynomialMap_injective (n + 1) σ
  rw [deltaDivisionFiniteRelationPolynomial_image,
    deltaDivisionIteratedRelation_eq_leading_add_lower]
  simp only [map_add, map_mul, relativeFreeFiniteInitialPolynomialMap,
    MvPolynomial.rename_C, MvPolynomial.rename_X, MvPolynomial.rename_rename,
    Function.comp_def, Fin.val_castSucc, Fin.val_last]

/-- p除算の実関係式の最高係数は全深さでp。 -/
theorem deltaPDivisionIteratedRelation_eq_leading_add_lower
    (D : DeltaStructure p A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionIteratedRelation D (p : A) a s n =
      (p : RelativeFreeDeltaRing (R := A) σ) * MvPolynomial.X (s, n) +
        relativeFreeFiniteInitialPolynomialMap n σ A
          (deltaDivisionFiniteLeadingLowerPolynomial D (p : A) a s n) := by
  have hp : D.frobeniusLift^[n] (p : A) = p := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_natCast]
  rw [deltaDivisionIteratedRelation_eq_leading_add_lower, hp, map_natCast]

end SerrePositivity.BhattScholze
