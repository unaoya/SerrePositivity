module
public import SerrePositivity.CommutativeAlgebra.MaximalRegularSequence

/-! # The prime dimension formula for regular local rings -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open RingTheory.Sequence
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- In a regular local ring every prime quotient satisfies the height dimension formula. -/
lemma regular_primeHeight_add_quotientDimension (p : PrimeSpectrum R) :
    (p.asIdeal.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim R := by
  obtain ⟨rs, q, hrs, _, hq, hpq, hr⟩ := exists_regularSequence_associatedPrime_above p
  have : q.IsPrime := hq.isPrime
  let Q : PrimeSpectrum R := ⟨q, inferInstance⟩
  have := finiteRingKrullDim_primeQuotient Q
  have hdim := RegularSequenceUnmixedness.dimension_eq rs hrs.toIsWeaklyRegular hq
  have hdimNat : dimToNat (ringKrullDim (R ⧸ q)) + rs.length = dimToNat (ringKrullDim R) := by
    rw [← natCast_dimToNat_ringKrullDim (R ⧸ q), ← natCast_dimToNat_ringKrullDim R] at hdim
    exact_mod_cast hdim
  have hupper := primeHeight_toNat_add_quotientDimToNat_le Q
  have hrNat : rs.length ≤ p.asIdeal.height.toNat := by
    rw [← natCast_primeHeight_toNat p] at hr
    exact_mod_cast hr
  have hmono : p.asIdeal.height.toNat ≤ q.height.toNat := by
    have hh := Ideal.height_mono hpq
    rw [← natCast_primeHeight_toNat p, ← natCast_primeHeight_toNat Q] at hh
    exact_mod_cast hh
  have hqNat : q.height.toNat = rs.length := by
    change q.height.toNat + dimToNat (ringKrullDim (R ⧸ q)) ≤ _ at hupper
    omega
  have heNat : q.height.toNat ≤ p.asIdeal.height.toNat := by omega
  have he : q.height ≤ p.asIdeal.height := by
    rw [← natCast_primeHeight_toNat Q, ← natCast_primeHeight_toNat p]
    exact_mod_cast heNat
  have hpqeq : p.asIdeal = q := Ideal.eq_of_le_of_height_le p.asIdeal hpq he
  have hpLen : p.asIdeal.height = (rs.length : ℕ∞) := by
    rw [← natCast_primeHeight_toNat p, hpqeq, hqNat]
  rw [hpLen, hpqeq, add_comm]
  exact RegularSequenceUnmixedness.dimension_eq rs hrs.toIsWeaklyRegular hq

/-- Natural-number form of the prime dimension formula. -/
lemma regular_primeHeight_toNat_add_quotientDimToNat (p : PrimeSpectrum R) :
    p.asIdeal.height.toNat + dimToNat (ringKrullDim (R ⧸ p.asIdeal)) =
      dimToNat (ringKrullDim R) := by
  have := finiteRingKrullDim_primeQuotient p
  have h := regular_primeHeight_add_quotientDimension p
  rw [← natCast_dimToNat_ringKrullDim (R ⧸ p.asIdeal),
    ← natCast_dimToNat_ringKrullDim R, ← natCast_primeHeight_toNat p] at h
  exact_mod_cast h

/-- The minimum height of the support, with the empty support assigned infinite codimension. -/
def supportCodimension (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] : ℕ∞ := ⨅ p ∈ Module.support R M, p.asIdeal.height

omit [IsRegularLocalRing R] in
lemma supportCodimension_le_height {M : Type u} [AddCommGroup M] [Module R M]
    {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) :
    supportCodimension R M ≤ p.asIdeal.height := iInf₂_le p hp

omit [IsRegularLocalRing R] in
/-- A point of the support contributes its entire upward prime interval to the support. -/
lemma primeQuotientDimension_le_supportDim {M : Type u} [AddCommGroup M] [Module R M]
    {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) :
    ringKrullDim (R ⧸ p.asIdeal) ≤ Module.supportDim R M := by
  rw [primeQuotientDimension_eq_coheight, Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_le_of_strictMono
    (fun q : Set.Ici p => (⟨q.val, Module.mem_support_mono q.property hp⟩ : Module.support R M))
    (fun _ _ h => h)

omit [IsRegularLocalRing R] in
/-- Quotient-dimension bounds at every supported point bound the dimension of the support. -/
lemma supportDim_le_of_primeQuotientDimension_le {M : Type u} [AddCommGroup M] [Module R M]
    (D : WithBot ℕ∞) (hD : ∀ p ∈ Module.support R M, ringKrullDim (R ⧸ p.asIdeal) ≤ D) :
    Module.supportDim R M ≤ D := by
  unfold Module.supportDim Order.krullDim
  refine iSup_le fun c => ?_
  let c' : LTSeries (PrimeSpectrum R) := LTSeries.mk c.length
    (fun i => (c i).val) (fun _ _ h => c.strictMono h)
  have hl : (c.length : WithBot ℕ∞) ≤ (Order.coheight c'.head : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr (Order.length_le_coheight_head (p := c'))
  exact hl.trans ((primeQuotientDimension_eq_coheight c'.head).symm.le.trans
    (hD c.head.val c.head.property))

/-- A nonempty support contains a prime of minimum height, whose quotient realizes its dimension. -/
lemma exists_minimumHeight_support_prime (M : Type u) [AddCommGroup M] [Module R M]
    [Nontrivial M] :
    ∃ p : PrimeSpectrum R, p ∈ Module.support R M ∧
      supportCodimension R M = p.asIdeal.height ∧
      Module.supportDim R M = ringKrullDim (R ⧸ p.asIdeal) := by
  classical
  have hex : ∃ n : ℕ, ∃ p : PrimeSpectrum R,
      p ∈ Module.support R M ∧ p.asIdeal.height.toNat = n := by
    obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := M)
    exact ⟨_, p, hp, rfl⟩
  obtain ⟨p, hp, hpn⟩ := Nat.find_spec hex
  have hmin : ∀ q ∈ Module.support R M, p.asIdeal.height.toNat ≤ q.asIdeal.height.toNat := by
    intro q hq
    rw [hpn]
    exact Nat.find_min' hex ⟨q, hq, rfl⟩
  have hcod : supportCodimension R M = p.asIdeal.height := by
    apply le_antisymm (supportCodimension_le_height hp)
    refine le_iInf fun q => le_iInf fun hq => ?_
    rw [← natCast_primeHeight_toNat p, ← natCast_primeHeight_toNat q]
    exact_mod_cast hmin q hq
  refine ⟨p, hp, hcod, le_antisymm ?_ (primeQuotientDimension_le_supportDim hp)⟩
  apply supportDim_le_of_primeQuotientDimension_le
  intro q hq
  have hpdim := regular_primeHeight_toNat_add_quotientDimToNat p
  have hqdim := regular_primeHeight_toNat_add_quotientDimToNat q
  have hm := hmin q hq
  have hd : dimToNat (ringKrullDim (R ⧸ q.asIdeal)) ≤
      dimToNat (ringKrullDim (R ⧸ p.asIdeal)) := by omega
  have := finiteRingKrullDim_primeQuotient p
  have := finiteRingKrullDim_primeQuotient q
  rw [← natCast_dimToNat_ringKrullDim (R ⧸ q.asIdeal),
    ← natCast_dimToNat_ringKrullDim (R ⧸ p.asIdeal)]
  exact_mod_cast hd

/-- The support codimension and support dimension add to the ring dimension. -/
lemma regular_supportCodimension_add_supportDim (M : Type u) [AddCommGroup M] [Module R M]
    [Nontrivial M] :
    (supportCodimension R M : WithBot ℕ∞) + Module.supportDim R M = ringKrullDim R := by
  obtain ⟨p, _, hcod, hdim⟩ := exists_minimumHeight_support_prime (R := R) M
  rw [hcod, hdim]
  exact regular_primeHeight_add_quotientDimension p

/-- Natural-number codimension formula for nonzero modules over regular local rings. -/
lemma regular_supportCodimension_toNat (M : Type u) [AddCommGroup M] [Module R M]
    [Nontrivial M] :
    (supportCodimension R M).toNat =
      dimToNat (ringKrullDim R) - dimToNat (Module.supportDim R M) := by
  obtain ⟨p, _, hcod, hdim⟩ := exists_minimumHeight_support_prime (R := R) M
  rw [hcod, hdim]
  have h := regular_primeHeight_toNat_add_quotientDimToNat p
  omega
end SerrePositivity
