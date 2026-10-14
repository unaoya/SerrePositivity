module

public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedNormalized
public import SerrePositivity.CLMST.Almost
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import SerrePositivity.CLMST.CyclicPLength
public import SerrePositivity.CLMST.CyclicUnitLength
public import SerrePositivity.CLMST.CyclicPPowerLength
public import SerrePositivity.CLMST.CyclicTorsionComparison
public import SerrePositivity.CLMST.CyclicPerfectoidization
public import SerrePositivity.CLMST.CyclicNormalizedBound

/-! # CLMSTの巡回加群の長さ評価への証明済み接続

CLMST Proposition 4.0.10の証明で使う巡回商の長さ零を、
正規化上界・p因子の除去・既存の単元と一元パラメータ系の評価から導く。
このファイル自身の長さ零のsorryは置かない。

標準perfectoid化への全射性は、BS Cor 7.3 / Theorem 7.4の
pねじれのない完備商への適用形を名前付きで引用する。
巡回商のpの非零因子性・完備性の確認と、選んだ普遍対象への全射性の移送は証明済み。
一般加群への帰着とalmost圏への接続は別のモジュールで証明する。
旧Inputsの公開入口は互換aliasとしてこの証明を参照する。

出典：https://arxiv.org/html/2209.04046v4 （Proposition 4.0.10の証明）。
全射性の引用：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf （§7.1）。
-/

public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2

/-- pで割れない非単元の長さ零。標準写像の全射性の条件を具体的に供給する。 -/
theorem cyclic_length_eq_zero_of_not_dvd
    (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]
    {r : ℕ} (t : Fin (r + 2) → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    (e : A ≃+* MvPowerSeries {i : Fin (r + 2) // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) (n : ℕ) :
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g))) = 0 := by
  exact completedLength_cyclic_pow_eq_zero_of_witt_of_surjective A k t p ht htp hdim e he
    hperf g hgm hpg
    (toPerfectoidization_cyclic_surjective_of_not_dvd A t p ht htp hdim hperf g hpg) n

/-- 標準混標数基底上で、極大イデアルの冪と非零 g の perfectoid ideal による巡回商は長さ零。
巡回商の数値評価を証明し、深い文献入力をBSのperfectoid化の基礎結果に分離する。 -/
theorem cyclic_length_eq_zero
    (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]
    {h : ℕ} (t : Fin h → A) (hpos : 0 < h) (htp : t ⟨0, hpos⟩ = (p : A))
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : g ≠ 0) (n : ℕ) :
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((CompletedTower A t p) ⧸
        ((completedTowerMaxIdeal A t p) ^ n ⊔
          perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g))) = 0 := by
  by_cases hgu : IsUnit g
  · exact completedLength_cyclic_unit_eq_zero A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) hperf g hgu n
  · by_cases hgp : g = (p : A)
    · subst g
      rw [show algebraMap A (CompletedTower A t p) (p : A) = (p : CompletedTower A t p)
        from map_natCast _ _]
      exact completedLength_cyclic_p_eq_zero A t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) ⟨0, hpos⟩ htp hperf n
    · by_cases hsmall : h = 1
      · subst h
        exact completedLength_cyclic_fin_one_eq_zero A t p ht htp hperf g hg n
      · have htwo : 2 ≤ h := by omega
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le htwo
        have hhr : h = r + 2 := by omega
        clear hr
        subst h
        have hdim' : ringKrullDim A = (r : ℕ∞) + 2 := by simpa using hdim
        have hp : (p : A) ∈ maximalIdeal A := by
          rw [← htp]
          exact ht ▸ Ideal.subset_span (Set.mem_range_self _)
        obtain ⟨c, g', hgg', hpg⟩ := exists_p_power_factor_of_nonzero A p hp g hg
        rw [completedLength_cyclic_pow_eq_of_p_factor A t p
          (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
          ⟨0, hpos⟩ htp hperf g g' c hgg' n]
        by_cases hunit : IsUnit g'
        · exact completedLength_cyclic_unit_eq_zero A t p
            (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) hperf g' hunit n
        · exact cyclic_length_eq_zero_of_not_dvd A k p (r := r) t ht htp hdim' e he hperf g'
            (by simpa only [mem_maximalIdeal, mem_nonunits_iff] using hunit) hpg n

end SerrePositivity.CLMST
