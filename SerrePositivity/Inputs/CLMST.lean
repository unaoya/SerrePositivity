module

public import SerrePositivity.Paper.Section2.MixedPerfectoid
public import SerrePositivity.Inputs.PerfectoidTower

/-! # CLMST の混標数の定理（文献からの引用）

Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert-Kunz multiplicity,
and an application to local fundamental groups*, arXiv:2209.04046v4。
出典：https://arxiv.org/html/2209.04046v4

`C_D = (R∞ ⊗[A] D)_perfd` と `(g)_perfd = ker(R∞ → (R∞/g)_perfd)` は
普遍性による定義を使う。引用するのは Corollary 4.0.4、Proposition 4.0.10 の零の場合、
Proposition 4.0.14 の `n = 0` の場合である。
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
引用：CLMST Proposition 4.0.10 の `N = 0` の場合。その証明は任意の非零 `g ∈ A` に適用でき、
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
  sorry

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
引用：CLMST Notation 4.0.1 における étale locus を切り出す `g` の存在と、Corollary 4.0.4
の `n = 0` の場合を合わせた主張。非零元の存在もこの名前付き引用に含める。
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
  sorry

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- パラメータ商の完備化した塔上の正規化長さは Hilbert–Samuel 重複度。
引用：CLMST Proposition 4.0.14 の `n = 0` の場合。`p^(-nh) = 1` に特殊化している。
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
  sorry

end SerrePositivity.Inputs
