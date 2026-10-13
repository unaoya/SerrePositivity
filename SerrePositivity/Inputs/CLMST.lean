module

public import SerrePositivity.Paper.Section2.MixedPerfectoid
public import SerrePositivity.Paper.Section2.CompletedTower
public import SerrePositivity.Inputs.PerfectoidTower
public import SerrePositivity.CLMST.NormalizedAlmostLength
public import SerrePositivity.CLMST.CohomologyVanishing
public import SerrePositivity.CLMST.ParameterLength

/-! # CLMST の混標数の定理の互換入口

Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert-Kunz multiplicity,
and an application to local fundamental groups*, arXiv:2209.04046v4。
出典：https://arxiv.org/html/2209.04046v4

三つの既存の署名を保持し、共通層の原典入力の適用を証明して公開する。
このファイルに直接の sorry はなく、文献入力は `CLMST/Inputs/` に分離した。

`C_D = (R∞ ⊗[A] D)_perfd` と `(g)_perfd = ker(R∞ → (R∞/g)_perfd)` は
普遍性による定義を使う。Corollary 4.0.4 の両成分・全段を Paper 非依存の層で引用し、
非零 g の選択と n=0 への適用は証明する。Proposition 4.0.14 も一般段を引用し、
零段の環同型・重複度の不変性を使ってこのファイルの主張へ適用する。
Proposition 4.0.10 については Paper 非依存の巡回評価を引用し、
このファイルの一般加群の長さ零はその評価への帰着として証明する。
これらの適用に必要な Koszul ホモロジーの冪ねじれと、完備化前の塔への長さの移送は
引用に含めず、`CompletedTower` と `MixedLengthAlgebra` で証明する。
-/

public section
universe u
open IsLocalRing
open scoped ENNReal
namespace SerrePositivity.Inputs
open Section2

/-- `(g)_perfd` に消される `m_A` 冪ねじれ加群は正規化長さ零。
CLMST Proposition 4.0.10 の零の場合への互換入口。巡回商の評価だけを
`CLMST.Inputs.AlmostLength` で引用し、一般加群への帰着は証明する。任意の非零 `g ∈ A` に適用でき、
有限拡大が `g` の外で étale であるという条件はこの命題には不要。 -/
theorem clmst_length_eq_zero_of_perfectoidIdeal_annihilates
    (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]
    {h : ℕ} (t : Fin h → A) (hpos : 0 < h) (htp : t ⟨0, hpos⟩ = (p : A))
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : g ≠ 0)
    (M : Type u) [AddCommGroup M] [Module (CompletedTower A t p) M]
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M)
    (hann : perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) ≤ Module.annihilator (CompletedTower A t p) M) :
    (completedTowerLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len M = 0 := by
  exact CLMST.completedLength_eq_zero_of_perfectoidIdeal_annihilates
    A k p t hpos htp ht hdim e he hperf g hg M hM hann

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 一つの非零 `g ∈ A` の perfectoid イデアルが、全パラメータ系の高次 Koszul ホモロジーを消す。
Corollary 4.0.4 の全段の主張を `CLMST.Inputs.CohomologyVanishing` で引用する。
非零 g の有限エタール化による選択と、零段の同型・パラメータの移送は
`CLMST.CohomologyVanishing` で証明する。ここはその既存利用先への互換入口である。
ここでは正規化長さの消滅はまだ結論にしない。 -/
theorem clmst_exists_perfectoidIdeal_annihilates_koszul :
    ∃ g : A, g ≠ 0 ∧ ∀ (z : Fin h → D), IsSystemOfParameters D z →
      ∀ i : ℕ, 0 < i →
        letI := Module.compHom
          (koszulHomologySelf (fun j ↦ algebraMap D (MixedPerfectoid A D t p hperf) (z j)) i)
          (algebraMap (CompletedTower A t p) (MixedPerfectoid A D t p hperf))
        perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g) ≤
          Module.annihilator (CompletedTower A t p)
            (koszulHomologySelf
              (fun j ↦ algebraMap D (MixedPerfectoid A D t p hperf) (z j)) i) := by
  exact CLMST.exists_perfectoidIdeal_annihilates_koszul
    A D hinj hres t hdimA hdimD hpos ht hsop p htp e he hperf

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- パラメータ商の完備化した塔上の正規化長さは Hilbert–Samuel 重複度。
CLMST Proposition 4.0.14 の一般 n の公式を `CLMST.Inputs.ParameterLength` で引用する。
`CLMST.ParameterLength` が n=0 への特殊化・商の一致・重複度の同型不変性を証明し、
ここはその既存利用先への互換入口である。
`C_D` は任意の未知の代数ではなく、上で普遍性から選んだ perfectoid 化である。 -/
theorem clmst_parameter_quotient_length
    (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    letI := Module.compHom
      ((MixedPerfectoid A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (MixedPerfectoid A D t p hperf) (z j)))
      (algebraMap (CompletedTower A t p) (MixedPerfectoid A D t p hperf))
    (completedTowerLength A t p (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((MixedPerfectoid A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (MixedPerfectoid A D t p hperf) (z j))) =
      ENNReal.ofReal (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
  exact CLMST.parameter_quotient_length
    A D hinj hres t hdimA hdimD hpos ht hsop p htp e he hperf z hz

end SerrePositivity.Inputs
