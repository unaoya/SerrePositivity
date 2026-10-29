module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionSubfield
public import SerrePositivity.FieldTheory.PBasisDifferentials
public import SerrePositivity.FieldTheory.PMonomialPartition

/-! # 共有限分数体上の微分基底と次元

底体Q_e=Frac(κ_e[[X]])の作用はX_i↦T_i^pで指定する。
既存の分数体単項式基底を相対p指数で添字付け直し、T_iと残した係数b_jの微分を基底にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity
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

omit [Fintype σ] in
/-- 共有限分数体上の通常微分の有限性は、微分基底から供給する。 -/
theorem IsPBasis.moduleFinite_cofiniteFractionDifferentialBasis [Finite σ]
    (hb : IsPBasis K p b) :
    letI : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
    letI : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
    Module.Finite K₀ (KaehlerDifferential Q K₀) := by
  let := Fintype.ofFinite σ
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  exact Module.Finite.of_basis (hb.cofiniteFractionDifferentialBasis e)

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

end SerrePositivity
