module

public import SerrePositivity.CLMST.CyclicLength
public import SerrePositivity.CLMST.AlmostLength
public import SerrePositivity.LengthAlgebra.Almost
public import SerrePositivity.CLMST.BasicSetup

/-! # CLMST の巡回評価から一般加群と almost 同型への接続

巡回商の長さ零はBSの存在・全射性からCyclicLengthで証明する。
上限の性質で一般加群への帰着を証明し、
実際の mod p^N の almost 圏での同型から正規化長さの一致を導く。
mod p^N のイデアルの冪等性は almost 圏を作るための別入力であり、
長さ零への帰着には不要である。
-/

@[expose] public section
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2 CategoryTheory

variable (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]
    {h : ℕ} (t : Fin h → A) (hpos : 0 < h) (htp : t ⟨0, hpos⟩ = (p : A))
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : g ≠ 0)

include hpos htp hdim e he hg in
/-- 巡回商の長さ評価から、一様な極大イデアル冪ねじれの almost zero 加群の長さ零を証明。
証明済みの巡回評価を一般加群へ使う部分は、上限と巡回像による被覆の一般論である。 -/
theorem completedLength_eq_zero_of_perfectoidIdeal_annihilates
    (M : Type u) [AddCommGroup M] [Module (CompletedTower A t p) M]
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M)
    (hann : Almost.IsAlmostZero
      (perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g)) M) :
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len M = 0 := by
  apply LengthAlgebra.length_eq_zero_of_cyclic_quotients _ _ _
    (RootTowerLength.completedNormalizedLength_hasSup A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))) _ M hM hann
  intro n
  exact cyclic_length_eq_zero A k p t hpos htp ht hdim e he hperf g hg n

include hpos htp ht in
omit [Fact p.Prime] in
/-- 長さの定義域の二つの加群を、同じ mod p^N の環の上で扱える。
共通指数の存在は基底の p の所属と一様な冪ねじれから証明する。 -/
theorem exists_common_completedTower_p_pow_annihilates
    (M M' : ModuleCat.{u} (CompletedTower A t p))
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M)
    (hM' : IsPowTorsion (completedTowerMaxIdeal A t p) M') :
    ∃ N : ℕ, Almost.IsAlmostZero (Ideal.span {(p : CompletedTower A t p) ^ N}) M ∧
      Almost.IsAlmostZero (Ideal.span {(p : CompletedTower A t p) ^ N}) M' := by
  apply exists_common_p_pow_annihilates (CompletedTower A t p) p
    (completedTowerMaxIdeal A t p) _ M M' hM hM'
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp, ← ht]
    exact Ideal.subset_span (Set.mem_range_self (⟨0, hpos⟩ : Fin h))
  simpa [completedTowerMaxIdeal] using
    Ideal.mem_map_of_mem (algebraMap A (CompletedTower A t p)) hp

include hpos htp hdim e he hg in
/-- CLMST Proposition 4.0.10 の mod p^N における実際の almost 同型から長さの一致。
M、M' は元の完備塔上の任意の冪ねじれ加群であり、商環作用を明示的に構成する。
巡回商の評価にはBSの存在・全射性を使い、mod p^Nのイデアル冪等性を別に引用する。
比較自体は一般論で証明する。 -/
theorem completedLength_eq_of_perfectoid_mod_almost_iso
    (N : ℕ) (M M' : ModuleCat.{u} (CompletedTower A t p))
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M)
    (hM' : IsPowTorsion (completedTowerMaxIdeal A t p) M')
    (hNM : Almost.IsAlmostZero (Ideal.span {(p : CompletedTower A t p) ^ N}) M)
    (hNM' : Almost.IsAlmostZero (Ideal.span {(p : CompletedTower A t p) ^ N}) M') :
    let _ := Almost.quotientModule (Ideal.span {(p : CompletedTower A t p) ^ N}) M hNM
    let _ := Almost.quotientModule (Ideal.span {(p : CompletedTower A t p) ^ N}) M' hNM'
    ((perfectoidAlmostModLocalization (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N).obj
        (ModuleCat.of ((CompletedTower A t p) ⧸ Ideal.span {(p : CompletedTower A t p) ^ N}) M) ≅
      (perfectoidAlmostModLocalization (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g) N).obj
          (ModuleCat.of
            ((CompletedTower A t p) ⧸ Ideal.span {(p : CompletedTower A t p) ^ N}) M')) →
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len M =
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len M' := by
  let : Fact (perfectoidIdealMod (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N *
    perfectoidIdealMod (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N =
    perfectoidIdealMod (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N) :=
    ⟨Inputs.perfectoidIdealMod_idempotent _ p hperf _ N⟩
  apply LengthAlgebra.length_eq_of_quotient_almost_iso
    (Ideal.span {(p : CompletedTower A t p) ^ N})
    (perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))
    (completedTowerMaxIdeal A t p)
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))) _ M M' hM hM' hNM hNM'
  intro X hX
  exact completedLength_eq_zero_of_perfectoidIdeal_annihilates
    A k p t hpos htp ht hdim e he hperf g hg X.obj X.property hX

end SerrePositivity.CLMST
