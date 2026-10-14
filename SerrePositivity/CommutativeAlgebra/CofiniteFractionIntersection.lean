module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionSubfield

/-! # 中間係数体に沿う分数体族の交わり

分母をp乗へ変えて全ての像に共通な分母を取り、基底の飽和性で分子を冪級数環へ戻す。
係数体の交わりとFrobeniusから、元が共通分数体のp乗であることを確認する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} {b : ι → K}

/-- 全ての中間係数体の冪級数写像の像に属す冪級数は、実際にp乗である。 -/
theorem IsPBasis.exists_powerSeries_pow_of_mem_all_cofinite_ranges
    (hb : IsPBasis K p b) (f : MvPowerSeries σ K)
    (hf : ∀ e : Finset ι, f ∈ Set.range
      (powerSeriesExpandMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
        (K := K) p (Fact.out : p.Prime).pos)) :
    ∃ g : MvPowerSeries σ K, g ^ p = f := by
  have hc (d : σ →₀ ℕ) : MvPowerSeries.coeff (p • d) f ∈ pPowerSubfield K p := by
    have hmem : MvPowerSeries.coeff (p • d) f ∈
        ⨅ e : Finset ι, pBasisCofiniteField (p := p) b e := by
      change MvPowerSeries.coeff (p • d) f ∈
        (⨅ e : Finset ι, pBasisCofiniteField (p := p) b e).toSubfield
      rw [IntermediateField.iInf_toSubfield]
      apply Subfield.mem_iInf.mpr
      intro e
      obtain ⟨v, hv⟩ := hf e
      have he := congrArg (MvPowerSeries.coeff (p • d)) hv
      change MvPowerSeries.coeff (p • d)
        (MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
          (MvPowerSeries.map (algebraMap (pBasisCofiniteField (p := p) b e) K) v)) = _ at he
      simp only [MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map] at he
      rw [← he]
      exact (MvPowerSeries.coeff d v).property
    rw [hb.iInf_cofiniteField_eq_bot] at hmem
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hmem
    rw [← ha]
    exact a.property
  obtain ⟨v, hv⟩ := hf ∅
  let ψ := MvPowerSeries.map (algebraMap (pBasisCofiniteField (p := p) b ∅) K) v
  have hψ : MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero ψ = f := hv
  let g : MvPowerSeries σ K := fun d ↦
    (pPowerEquiv K p).symm ⟨MvPowerSeries.coeff (p • d) f, hc d⟩
  have hm : MvPowerSeries.map (frobenius K p) g = ψ := by
    ext d
    have hp := congrArg Subtype.val
      ((pPowerEquiv K p).apply_symm_apply ⟨MvPowerSeries.coeff (p • d) f, hc d⟩)
    change (g d) ^ p = MvPowerSeries.coeff d ψ
    calc
      _ = MvPowerSeries.coeff (p • d) f := hp
      _ = MvPowerSeries.coeff d ψ := by
        rw [← hψ, MvPowerSeries.coeff_expand_smul]
  refine ⟨g, ?_⟩
  calc
    g ^ p = MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
        (MvPowerSeries.map (frobenius K p) g) := by
      rw [← MvPowerSeries.map_expand]
      exact (MvPowerSeries.map_frobenius_expand p (Fact.out : p.Prime).ne_zero).symm
    _ = MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero ψ := congrArg _ hm
    _ = f := hψ

/-- 全ての実際の像の部分体に属す元は、共通分数体で実際にp乗である。 -/
theorem IsPBasis.mem_pPowerSubfield_of_mem_all_cofiniteFractionSubfields [Finite σ]
    (hb : IsPBasis K p b) (x : FractionRing (MvPowerSeries σ K))
    (hx : ∀ e : Finset ι, x ∈ pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e) :
    x ∈ pPowerSubfield (FractionRing (MvPowerSeries σ K)) p := by
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (MvPowerSeries σ K) x
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  have hgL : algebraMap _ (FractionRing (MvPowerSeries σ K)) g ≠ 0 := by
    intro h
    apply hg0
    apply IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
    simpa only [map_zero] using h
  let n := f * g ^ (p - 1)
  have hpow : (algebraMap _ (FractionRing (MvPowerSeries σ K)) g) ^ p =
      (algebraMap _ (FractionRing (MvPowerSeries σ K)) g) ^ (p - 1) *
        algebraMap _ (FractionRing (MvPowerSeries σ K)) g := by
    conv_lhs => rw [← Nat.sub_add_cancel (Fact.out : p.Prime).pos]
    rw [pow_succ]
  have hnEq : algebraMap _ (FractionRing (MvPowerSeries σ K)) n =
      (algebraMap _ (FractionRing (MvPowerSeries σ K)) f /
        algebraMap _ (FractionRing (MvPowerSeries σ K)) g) *
          (algebraMap _ (FractionRing (MvPowerSeries σ K)) g) ^ p := by
    rw [hpow]
    change algebraMap _ (FractionRing (MvPowerSeries σ K)) (f * g ^ (p - 1)) = _
    rw [map_mul, map_pow]
    field_simp [hgL]
  have hn (e : Finset ι) : algebraMap _ (FractionRing (MvPowerSeries σ K)) n ∈
      pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e := by
    rw [hnEq]
    apply Subfield.mul_mem _ (hx e)
    apply pPowerSubfield_le_cofiniteFractionSubfield b e
    exact (mem_pPowerSubfield _ p _).mpr ⟨_, rfl⟩
  have hnRange (e : Finset ι) : n ∈ Set.range
      (powerSeriesExpandMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
        (K := K) p (Fact.out : p.Prime).pos) := by
    have hB0 : hb.cofiniteMonomialBasis e 0 = 1 := by simp
    exact (algebraMap_mem_powerSeriesFractionSubfield_iff_of_basis_one
      (hb.cofiniteMonomialBasis e) 0 hB0 p (Fact.out : p.Prime).pos n).mp (hn e)
  obtain ⟨u, hu⟩ := hb.exists_powerSeries_pow_of_mem_all_cofinite_ranges n hnRange
  apply (mem_pPowerSubfield _ p _).mpr
  refine ⟨algebraMap _ (FractionRing (MvPowerSeries σ K)) u /
    algebraMap _ (FractionRing (MvPowerSeries σ K)) g, ?_⟩
  calc
    _ = algebraMap _ (FractionRing (MvPowerSeries σ K)) n /
        (algebraMap _ (FractionRing (MvPowerSeries σ K)) g) ^ p := by
      rw [div_pow, ← map_pow, hu]
    _ = _ := (div_eq_iff (pow_ne_zero _ hgL)).mpr hnEq

/-- 有限変数では、実際の像の部分体族の交わりは共通分数体のp乗部分体。 -/
theorem IsPBasis.iInf_cofiniteFractionSubfield_eq_pPower [Finite σ]
    (hb : IsPBasis K p b) :
    (⨅ e : Finset ι, pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e) =
      pPowerSubfield (FractionRing (MvPowerSeries σ K)) p := by
  apply le_antisymm ?_ (pPowerSubfield_le_iInf_cofiniteFractionSubfield b)
  intro x hx
  exact hb.mem_pPowerSubfield_of_mem_all_cofiniteFractionSubfields x (Subfield.mem_iInf.mp hx)

/-- p乗でない元は、実際の共有限分数体族の少なくとも一つに属さない。
この非所属からその部分体上の微分の非零性を得る判定は別に必要。 -/
theorem IsPBasis.exists_not_mem_cofiniteFractionSubfield [Finite σ]
    (hb : IsPBasis K p b) (x : FractionRing (MvPowerSeries σ K))
    (hx : x ∉ pPowerSubfield (FractionRing (MvPowerSeries σ K)) p) :
    ∃ e : Finset ι, x ∉ pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e := by
  classical
  by_contra h
  apply hx
  rw [← hb.iInf_cofiniteFractionSubfield_eq_pPower]
  apply Subfield.mem_iInf.mpr
  simpa only [not_exists, not_not] using h

end SerrePositivity
