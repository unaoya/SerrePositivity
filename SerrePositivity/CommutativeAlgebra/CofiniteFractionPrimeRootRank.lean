module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionDifferential
public import SerrePositivity.FieldTheory.SubfieldFamilyDifferentialRank

/-! # 実際の共有限分数体族に対する次数pの階数安定

交わりから選んだ指標より小さい任意の共有限な部分体について、
p乗根添加の通常微分の次元等号を得る。終域への作用は同じ指定済みの代数作用を使う。
一般の有限拡大への帰納は別の課題。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ ι L : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  [Finite σ] {b : ι → K} [Field L]
  [Algebra (FractionRing (MvPowerSeries σ K)) L] [CharP L p]

/-- 次数pの拡大では、十分小さい実際の部分体を選ぶと、その下の任意の共有限底体で次元が等しい。 -/
theorem IsPBasis.exists_cofiniteFractionSubfield_primeRoot_rank_stable
    (hb : IsPBasis K p b) (x : L) (a : FractionRing (MvPowerSeries σ K))
    (hpow : x ^ p = algebraMap (FractionRing (MvPowerSeries σ K)) L a)
    (hx : x ∉ Set.range (algebraMap (FractionRing (MvPowerSeries σ K)) L))
    (hs : Algebra.adjoin (FractionRing (MvPowerSeries σ K)) {x} = ⊤) :
    ∃ e : Finset ι, ∀ R : Subfield (FractionRing (MvPowerSeries σ K)),
      Module.Finite R (FractionRing (MvPowerSeries σ K)) →
      R ≤ pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e →
      letI : Algebra R L :=
        ((algebraMap (FractionRing (MvPowerSeries σ K)) L).comp
          (algebraMap R (FractionRing (MvPowerSeries σ K)))).toAlgebra
      letI : Module R L :=
        @Algebra.toModule _ _ _ _ (inferInstance : Algebra R L)
      letI : SMul R L := (inferInstance : Algebra R L).toSMul
      Module.finrank L (KaehlerDifferential R L) =
        Module.finrank (FractionRing (MvPowerSeries σ K))
          (KaehlerDifferential R (FractionRing (MvPowerSeries σ K))) := by
  exact exists_subfieldFamily_primeRoot_rank_stable
    (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b)
    (hb.finite_cofiniteFractionSubfield)
    (pPowerSubfield_le_cofiniteFractionSubfield b)
    hb.iInf_cofiniteFractionSubfield_eq_pPower x a hpow hx hs

end SerrePositivity
