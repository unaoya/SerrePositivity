module

public import SerrePositivity.CLMST.CyclicFactorReduction
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionPerfectoid
public import SerrePositivity.LengthAlgebra.RootTowerLength.CoordinateModuleVanishing

/-! # pねじれ商のperfectoid性から差の長さ零への接続

g=p^c g'のperfectoid化でpねじれを除いた商がperfectoidなら、普遍性によって
(g')_perfdの像がpねじれとなる。その像はpの全ての根で消えるため、差の長さは零。
商のperfectoid性を四条件から供給し、p因子の除去を無条件の長さ比較へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2 RootTowerLength

/-- p因子を除去しても、任意の冪の巡回商の正規化長さは変わらない。
pねじれ商のperfectoid性を内部で供給し、座標根による共通の長さ零判定を適用する。 -/
theorem completedLength_cyclic_pow_eq_of_p_factor
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (i : Fin h) (hti : t i = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g g' : A) (c : ℕ) (hg : g = (p : A) ^ c * g')
    (a : ℕ) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      ((completedTowerMaxIdeal A t p) ^ a ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      ((completedTowerMaxIdeal A t p) ^ a ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g'))) := by
  let C := CompletedTower A t p
  let : Algebra.FinitePresentation C (C ⧸ Ideal.span {algebraMap A C g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton (algebraMap A C g))
  let S := perfectoidQuotient C p hperf (algebraMap A C g)
  let κ : C →+* S := (toQuotientPerfectoidization C (Ideal.span {algebraMap A C g}) p hperf).comp
    (Ideal.Quotient.mk (Ideal.span {algebraMap A C g}))
  have hS : IsIntegralPerfectoid S p :=
    (isPerfectoidization_toQuotientPerfectoidization C (Ideal.span {algebraMap A C g}) p hperf).1
  have hQ : IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p :=
    hS.pTorsionQuotient_isIntegralPerfectoid S p
  have hgzero : (p : S) ^ c * κ (algebraMap A C g') = 0 := by
    have hh := (span_le_perfectoidIdeal C p hperf (algebraMap A C g))
      (Ideal.subset_span (Set.mem_singleton _))
    change κ (algebraMap A C g) = 0 at hh
    simpa only [hg, map_mul, map_pow, map_natCast] using hh
  apply completedNormalizedLength_quotient_pow_eq_of_coordinateRoot_mul A t p ht
    (hti ▸ ht i) i _ _ (perfectoidIdeal_le_of_p_power_factor A t p hperf g g' c hg) _ a
  intro n b hb
  have hpb : (p : S) * κ b = 0 :=
    perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid C S p
      hperf hS hQ κ (algebraMap A C g') c hgzero b hb
  have hρ : κ (completedTowerRoot A t p n i) ^ (p ^ n) = (p : S) := by
    rw [← map_pow, completedTowerRoot_pow, hti, map_natCast, map_natCast]
  change κ (completedTowerRoot A t p n i * b) = 0
  rw [map_mul]
  exact hS.p_power_root_mul_eq_zero_of_pow_mul_eq_zero S p _ n hρ 1 (κ b)
    (by simpa only [pow_one] using hpb)

end SerrePositivity.CLMST
