module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Expansion
public import SerrePositivity.FieldTheory.PBasisCofiniteField
public import SerrePositivity.CommutativeAlgebra.PowerSeries.FractionField
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.FieldTheory.PBasisDifferentials
public import SerrePositivity.FieldTheory.PExponent
public import SerrePositivity.FieldTheory.SubfieldFamilyDifferentialRank

/-! # 中間係数体に沿う冪級数の分数体の族

概要：体 `K` の p 基底 `b` と有限集合 `e`、有限変数 `σ` について、`K_e[[X]] → K[[T]]`（係数の包含と `X_i ↦ T_i^p`）
を考える。
- この写像は有限単射で、`K[[T]]` は `T^r · bᵈ`（`r_i < p`、`d` は `e` 上の p 指数）を基底に持つ。
  分数体へ移すと `[Frac K[[T]] : Frac K_e[[X]]] = p^{|σ| + |e|}`。
- 像の部分体 `F_e ⊆ K₀ = Frac K[[T]]` は `e` について反単調・下向き有向で、`K₀^p` を含み、全ての `e` での交わりは `K₀^p`。
- `F_e` 上の `K₀` の微分は `dT_i` と `db_j`（`j ∈ e`）を基底に持ち、次元は `|σ| + |e|`。
- 有限拡大 `L/K₀` について、十分大きな `f` 以降、`F_f` 上の `L` と `K₀` の微分の次元は等しい。
方針：交わりは、共通の分母を `p` 乗に取り替えて分子を冪級数に戻し、`K_e` の交わり `K^p`（`IsPBasis.iInf_cofiniteField_eq_bot`）
と Frobenius から各係数を `p` 乗とする。次元の安定は部分体の族の一般論（FieldTheory の `SubfieldFamilyDifferentialRank`）。
規約：分数体の写像は `powerSeriesFractionMap`（`fractionRingMap` の延長）で与える。
使われ方：固定した正規化での完備微分の次元計算（`CofiniteNormalization`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section PowerSeries

variable {K σ : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} {b : ι → K}

/-- κ_e[[X]]→κ[[T]]、X_i↦T_i^pは同じ係数写像を保つ有限単射。 -/
theorem IsPBasis.powerSeries_cofinite_expand_injective_finite [Finite σ]
    (hb : IsPBasis K p b) (e : Finset ι) :
    Function.Injective
      (powerSeriesExpandMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
        (K := K) p (Fact.out : p.Prime).pos) ∧
      (powerSeriesExpandMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
        (K := K) p (Fact.out : p.Prime).pos).Finite := by
  exact ⟨powerSeriesExpandMap_injective p (Fact.out : p.Prime).pos (RingHom.injective _),
    powerSeriesExpandMap_finite (hb.cofiniteMonomialBasis e) p (Fact.out : p.Prime).pos⟩

end PowerSeries

section Basis

variable {K σ : Type*} [Field K] [Fintype σ] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} {b : ι → K}

/-- 同じ有限単項式の像から構成した、中間係数体に沿う分数体の基底。 -/
def IsPBasis.cofiniteFractionBasis (hb : IsPBasis K p b) (e : Finset ι) :
    letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      powerSeriesFractionModule p (Fact.out : p.Prime).pos
    Module.Basis ((σ → Fin p) × PExponent p e)
      (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) :=
  powerSeriesFractionBasis p (Fact.out : p.Prime).pos (hb.cofiniteMonomialBasis e)

@[simp] theorem IsPBasis.cofiniteFractionBasis_apply
    (hb : IsPBasis K p b) (e : Finset ι) (x : (σ → Fin p) × PExponent p e) :
    hb.cofiniteFractionBasis (σ := σ) e x =
      algebraMap _ (FractionRing (MvPowerSeries σ K))
        (MvPowerSeries.monomial (powerSeriesResidueExponent p x.1)
          (pMonomial (fun i : e ↦ b i) x.2)) := by
  exact (powerSeriesFractionBasis_apply p (Fact.out : p.Prime).pos
    (hb.cofiniteMonomialBasis e) x).trans
      (congrArg (fun c ↦ algebraMap _ (FractionRing (MvPowerSeries σ K))
        (MvPowerSeries.monomial _ c)) (hb.cofiniteMonomialBasis_apply e x.2))

/-- 中間係数体と変数のp乗に沿う分数体拡大の正確な次数。 -/
theorem IsPBasis.finrank_cofiniteFractionField (hb : IsPBasis K p b) (e : Finset ι) :
    letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      powerSeriesFractionModule p (Fact.out : p.Prime).pos
    Module.finrank (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) = p ^ (Fintype.card σ + e.card) := by
  let : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) :=
    (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  rw [finrank_powerSeriesFractionField p (Fact.out : p.Prime).pos (hb.cofiniteMonomialBasis e)]
  rw [Nat.card_eq_fintype_card, PExponent.card, Fintype.card_coe, pow_add]

end Basis

section Subfield

variable {K σ : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} (b : ι → K)

/-- 共通のFrac(κ[[T]])内で、中間係数体に沿う分数体写像の実際の像。 -/
def pBasisCofiniteFractionSubfield (e : Finset ι) :
    Subfield (FractionRing (MvPowerSeries σ K)) :=
  powerSeriesFractionSubfield (pBasisCofiniteField (p := p) b e) p (Fact.out : p.Prime).pos

/-- 各係数のp乗を、κ_eの元として取る実際の係数写像。 -/
def cofiniteFrobeniusCoefficientMap (e : Finset ι) :
    K →+* pBasisCofiniteField (p := p) b e :=
  (algebraMap (pPowerSubfield K p) (pBasisCofiniteField (p := p) b e)).comp
    (frobenius K p).rangeRestrictField

/-- 係数のp乗と変数のp乗を合わせると、共通分数体のFrobeniusになる。 -/
theorem cofiniteFractionMap_comp_frobeniusCoefficientMap (e : Finset ι) :
    (powerSeriesFractionMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
      (K := K) p (Fact.out : p.Prime).pos).comp
      (powerSeriesCoefficientFractionMap (cofiniteFrobeniusCoefficientMap b e)) =
      frobenius (FractionRing (MvPowerSeries σ K)) p := by
  apply IsFractionRing.ringHom_ext (A := MvPowerSeries σ K)
  intro f
  simp only [RingHom.comp_apply, powerSeriesCoefficientFractionMap_algebraMap,
    powerSeriesFractionMap_algebraMap, frobenius_def, ← map_pow]
  congr 1
  have hc : (algebraMap (pBasisCofiniteField (p := p) b e) K).comp
      (cofiniteFrobeniusCoefficientMap b e) = frobenius K p := by ext x; rfl
  change MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
      (MvPowerSeries.map (algebraMap (pBasisCofiniteField (p := p) b e) K)
        (MvPowerSeries.map (cofiniteFrobeniusCoefficientMap b e) f)) = f ^ p
  rw [MvPowerSeries.map_map, hc, ← MvPowerSeries.map_expand]
  exact MvPowerSeries.map_frobenius_expand p (Fact.out : p.Prime).ne_zero

/-- 共通分数体のp乗部分体は、各実際の像の部分体に含まれる。 -/
theorem pPowerSubfield_le_cofiniteFractionSubfield (e : Finset ι) :
    pPowerSubfield (FractionRing (MvPowerSeries σ K)) p ≤
      pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e := by
  rintro x ⟨a, rfl⟩
  refine ⟨powerSeriesCoefficientFractionMap (cofiniteFrobeniusCoefficientMap b e) a, ?_⟩
  exact congrArg (fun f ↦ f a) (cofiniteFractionMap_comp_frobeniusCoefficientMap b e)

/-- 全ての実際の像の交わりに、p乗部分体が含まれる。逆包含は交わりの別モジュールで証明する。 -/
theorem pPowerSubfield_le_iInf_cofiniteFractionSubfield :
    pPowerSubfield (FractionRing (MvPowerSeries σ K)) p ≤
      ⨅ e : Finset ι, pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e :=
  le_iInf (pPowerSubfield_le_cofiniteFractionSubfield b)

/-- 残す方向を増やすと、共通分数体内の像も小さくなる。 -/
theorem pBasisCofiniteFractionSubfield_antitone {e f : Finset ι} (hef : e ⊆ f) :
    pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f ≤
      pBasisCofiniteFractionSubfield b e := by
  let φ := (IntermediateField.inclusion (pBasisCofiniteField_antitone (p := p) b hef)).toRingHom
  exact powerSeriesFractionSubfield_le_of_coefficientMap φ rfl p (Fact.out : p.Prime).pos

/-- 有限集合の和を使い、実際の像の部分体族は下向きに有向。 -/
theorem pBasisCofiniteFractionSubfield_directed :
    Directed (· ≥ ·) (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b) := by
  classical
  intro e f
  exact ⟨e ∪ f, pBasisCofiniteFractionSubfield_antitone b Finset.subset_union_left,
    pBasisCofiniteFractionSubfield_antitone b Finset.subset_union_right⟩

variable {b}

/-- 実際の像の部分体上でも、分数体の拡大次数はp^(h+|e|)。 -/
theorem IsPBasis.finrank_cofiniteFractionSubfield [Fintype σ]
    (hb : IsPBasis K p b) (e : Finset ι) :
    Module.finrank (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) = p ^ (Fintype.card σ + e.card) := by
  exact (finrank_fieldRange
    (powerSeriesFractionMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
      (K := K) p (Fact.out : p.Prime).pos)).trans (hb.finrank_cofiniteFractionField e)

/-- 各実際の像の部分体上で、共通分数体は有限次元。 -/
theorem IsPBasis.finite_cofiniteFractionSubfield [Finite σ]
    (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Finite (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) := by
  let : Fintype σ := Fintype.ofFinite σ
  apply Module.finite_of_finrank_pos
  rw [hb.finrank_cofiniteFractionSubfield e]
  exact pow_pos (Fact.out : p.Prime).pos _

end Subfield

section Intersection

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

end Intersection

section Differential

variable {K σ ι : Type*} [Field K] [Fintype σ] {p : ℕ} [Fact p.Prime] [CharP K p]
  (b : ι → K) (e : Finset ι)

/-- 分数体内の変数と残した係数方向を合わせた族。 -/
def cofiniteFractionGenerators : σ ⊕ e → FractionRing (MvPowerSeries σ K) :=
  Sum.elim (fun i ↦ algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (MvPowerSeries.X i))
    (fun j ↦ algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (MvPowerSeries.C (b j)))

/-- 相対p指数と既存の分数体基底の添字の同値。 -/
def cofiniteFractionExponentEquiv :
    PExponent p (σ ⊕ e) ≃ (σ → Fin p) × PExponent p e :=
  PExponent.sumEquiv.trans (Equiv.prodCongr PExponent.equivFin (Equiv.refl _))

omit [Fact p.Prime] [CharP K p] in
/-- 相対p単項式は、既存の変数・係数単項式と同じ元。 -/
theorem pMonomial_cofiniteFractionGenerators (d : PExponent p (σ ⊕ e)) :
    pMonomial (cofiniteFractionGenerators (σ := σ) b e) d =
      algebraMap _ (FractionRing (MvPowerSeries σ K))
        (MvPowerSeries.monomial (powerSeriesResidueExponent p
          (cofiniteFractionExponentEquiv (σ := σ) (p := p) e d).1)
          (pMonomial (fun j : e ↦ b j)
            (cofiniteFractionExponentEquiv (σ := σ) (p := p) e d).2)) := by
  let z := PExponent.sumEquiv (p := p) (ι := σ) (κ := e) d
  have hd : d = PExponent.sumElim z.1 z.2 :=
    (PExponent.sumEquiv.symm_apply_apply d).symm
  have hr : powerSeriesResidueExponent p (PExponent.equivFin z.1) = z.1.val := by
    ext i
    rfl
  change pMonomial (cofiniteFractionGenerators b e) d =
    algebraMap _ _ (MvPowerSeries.monomial (powerSeriesResidueExponent p
      (PExponent.equivFin z.1)) (pMonomial (fun j : e ↦ b j) z.2))
  rw [hd, pMonomial_sumElim, hr, MvPowerSeries.monomial_eq', map_mul]
  simp only [pMonomial, cofiniteFractionGenerators, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr, map_finsuppProd, map_pow]
  rw [mul_comm]

variable {b}
local notation "Q" => FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
local notation "K₀" => FractionRing (MvPowerSeries σ K)

/-- 既存の分数体基底を、変数と係数方向の相対p単項式で添字付ける。 -/
def IsPBasis.cofiniteFractionMonomialBasis (hb : IsPBasis K p b) :
    letI : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
    Module.Basis (PExponent p (σ ⊕ e)) Q K₀ := by
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  exact (hb.cofiniteFractionBasis e).reindex (cofiniteFractionExponentEquiv e).symm

@[simp] theorem IsPBasis.cofiniteFractionMonomialBasis_apply (hb : IsPBasis K p b)
    (d : PExponent p (σ ⊕ e)) :
    letI : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
    hb.cofiniteFractionMonomialBasis e d =
      pMonomial (cofiniteFractionGenerators (σ := σ) b e) d := by
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  rw [IsPBasis.cofiniteFractionMonomialBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm, IsPBasis.cofiniteFractionBasis_apply]
  exact (pMonomial_cofiniteFractionGenerators b e d).symm

omit [Fintype σ] in
/-- 各方向のp乗は、指定されたQ_e→K₀の像に属する。 -/
theorem cofiniteFractionGenerators_pow_mem (j : σ ⊕ e) :
    letI : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    ∃ a : Q, cofiniteFractionGenerators b e j ^ p = algebraMap Q K₀ a := by
  obtain ⟨a, ha⟩ := pPowerSubfield_le_cofiniteFractionSubfield (σ := σ) b e
    ((mem_pPowerSubfield K₀ p _).mpr ⟨cofiniteFractionGenerators b e j, rfl⟩)
  exact ⟨a, ha.symm⟩

/-- T_iと残したb_jの微分からなる、同じQ_e上の通常微分の基底。 -/
def IsPBasis.cofiniteFractionDifferentialBasis (hb : IsPBasis K p b) :
    letI : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
    letI : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
    Module.Basis (σ ⊕ e) K₀ (KaehlerDifferential Q K₀) := by
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  exact kaehlerBasisOfPMonomialBasis (hb.cofiniteFractionMonomialBasis e)
    (hb.cofiniteFractionMonomialBasis_apply e) (cofiniteFractionGenerators_pow_mem (b := b) e)

@[simp] theorem IsPBasis.cofiniteFractionDifferentialBasis_apply (hb : IsPBasis K p b)
    (j : σ ⊕ e) :
    letI : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
    letI : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
    hb.cofiniteFractionDifferentialBasis e j =
      KaehlerDifferential.D Q K₀ (cofiniteFractionGenerators b e j) := by
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  exact kaehlerBasisOfPMonomialBasis_apply (hb.cofiniteFractionMonomialBasis e)
    (hb.cofiniteFractionMonomialBasis_apply e) (cofiniteFractionGenerators_pow_mem (b := b) e) j

/-- 共有限分数体上の通常微分の次元は、変数数と残した係数方向の数の和。 -/
theorem IsPBasis.finrank_cofiniteFractionDifferential (hb : IsPBasis K p b) :
    letI : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
    letI : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
    Module.finrank K₀ (KaehlerDifferential Q K₀) = Fintype.card σ + e.card := by
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  rw [Module.finrank_eq_card_basis (hb.cofiniteFractionDifferentialBasis e)]
  simp

end Differential

section Rank

variable {K σ ι L : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  [Finite σ] {b : ι → K} [Field L]
  [Algebra (FractionRing (MvPowerSeries σ K)) L] [CharP L p]
  [Module.Finite (FractionRing (MvPowerSeries σ K)) L]

/-- 実際の像の部分体を与える分数体そのものを底体として、同じ作用で階数安定を適用する。 -/
theorem IsPBasis.exists_cofiniteFractionField_rank_stable (hb : IsPBasis K p b) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
      letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) := powerSeriesFractionModule p (Fact.out : p.Prime).pos
      letI : SMul (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (inferInstance : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K))).toSMul
      letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L :=
        ((algebraMap (FractionRing (MvPowerSeries σ K)) L).comp
          (powerSeriesFractionMap p (Fact.out : p.Prime).pos)).toAlgebra
      letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L :=
        @Algebra.toModule _ _ _ _ (inferInstance :
          Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L)
      letI : SMul (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L :=
        (inferInstance : Algebra
          (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L).toSMul
      Module.finrank L (KaehlerDifferential
        (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L) =
        Module.finrank (FractionRing (MvPowerSeries σ K)) (KaehlerDifferential
          (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K))) := by
  let := Fintype.ofFinite σ
  obtain ⟨e, he⟩ := exists_subfieldFamily_rank_stable_of_finite
    (K := FractionRing (MvPowerSeries σ K)) (L := L)
    (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b) hb.finite_cofiniteFractionSubfield
    (pBasisCofiniteFractionSubfield_directed b)
    (pPowerSubfield_le_cofiniteFractionSubfield b) hb.iInf_cofiniteFractionSubfield_eq_pPower
  refine ⟨e, ?_⟩
  intro f hf
  let Q := FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))
  let K₀ := FractionRing (MvPowerSeries σ K)
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  let : Algebra Q L := ((algebraMap K₀ L).comp
    (powerSeriesFractionMap p (Fact.out : p.Prime).pos)).toAlgebra
  let : Module Q L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra Q L)
  let : SMul Q L := (inferInstance : Algebra Q L).toSMul
  let : IsScalarTower Q K₀ L := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite Q K₀ := Module.Finite.of_basis (hb.cofiniteFractionBasis (σ := σ) f)
  apply he Q
  rintro _ ⟨q, rfl⟩
  exact pBasisCofiniteFractionSubfield_antitone b hf ⟨q, rfl⟩

end Rank

end SerrePositivity
