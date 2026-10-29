module

public import SerrePositivity.FieldTheory.ExponentOneDifferentialConstants
public import SerrePositivity.CommutativeAlgebra.CofiniteFractionIntersection

/-! # 実際の共有限分数体族による微分の検出

各部分体の有限性・p乗部分体の包含を確認して相対微分の零判定を適用する。
交わりから検出する指標を選び、より小さい部分体でも非零性が保たれることを確認する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ ι : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  [Finite σ] {b : ι → K}

/-- 実際の分数体族の各部分体上で、微分が零になる元はその部分体の元だけ。 -/
theorem IsPBasis.kaehlerDifferential_cofiniteFractionSubfield_eq_zero_iff
    (hb : IsPBasis K p b) (e : Finset ι) (x : FractionRing (MvPowerSeries σ K)) :
    KaehlerDifferential.D (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) x = 0 ↔
        x ∈ pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e := by
  let : Module.Finite (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) := hb.finite_cofiniteFractionSubfield e
  exact kaehlerDifferential_finite_subfield_eq_zero_iff _
    (pPowerSubfield_le_cofiniteFractionSubfield b e) x

/-- p乗でない元を検出する指標を、指定済みの実際の部分体族から選ぶ。 -/
theorem IsPBasis.exists_kaehlerDifferential_cofiniteFractionSubfield_ne_zero
    (hb : IsPBasis K p b) (x : FractionRing (MvPowerSeries σ K))
    (hx : x ∉ pPowerSubfield (FractionRing (MvPowerSeries σ K)) p) :
    ∃ e : Finset ι, KaehlerDifferential.D
      (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) x ≠ 0 := by
  obtain ⟨e, he⟩ := hb.exists_not_mem_cofiniteFractionSubfield x hx
  exact ⟨e, fun h ↦ he ((hb.kaehlerDifferential_cofiniteFractionSubfield_eq_zero_iff e x).mp h)⟩

/-- より多くの方向を残して底体を小さくしても、検出した微分の非零性は保たれる。 -/
theorem IsPBasis.kaehlerDifferential_cofiniteFractionSubfield_ne_zero_of_subset
    (hb : IsPBasis K p b) {e f : Finset ι} (hef : e ⊆ f)
    (x : FractionRing (MvPowerSeries σ K))
    (hx : KaehlerDifferential.D (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) x ≠ 0) :
    KaehlerDifferential.D (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f)
      (FractionRing (MvPowerSeries σ K)) x ≠ 0 := by
  intro h
  have hf := (hb.kaehlerDifferential_cofiniteFractionSubfield_eq_zero_iff f x).mp h
  have he := pBasisCofiniteFractionSubfield_antitone b hef hf
  exact hx ((hb.kaehlerDifferential_cofiniteFractionSubfield_eq_zero_iff e x).mpr he)

end SerrePositivity
