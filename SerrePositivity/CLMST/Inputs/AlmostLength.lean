module

public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedNormalized
public import SerrePositivity.CLMST.Almost
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import SerrePositivity.CLMST.CyclicPLength
public import SerrePositivity.CLMST.CyclicUnitLength
public import SerrePositivity.CLMST.CyclicFactorReduction

/-! # CLMST の巡回加群の長さ評価（文献入力）

CLMST arXiv:2209.04046v4, Proposition 4.0.10 の証明で使う
`A∞ / (m_A^n + (g)_perfd)` の長さ零だけを引用する。
これは命題全体の almost 同型不変性のステートメントではなく、その証明の中間評価である。
一般加群への帰着と almost 圏への接続は別のモジュールで証明する。
単元とg=pの評価は証明済み。pがgを割らない非単元のmod p比較・正規化評価は
`CyclicNormalizedBound`でperfectoid化の全射性を条件として証明済み。
標準Witt表示からこの条件付き評価への接続もある。一元パラメータ系のpで割れない場合も証明済み。
g=p^c g'の有限分解と、その後の長さの帰着は明示した。残る引用には、
perfectoid化への全射性の確認と、差の核をp-almost zeroにするイデアル包含の確認が含まれる。
原典の閉包付きperfectoid idealをkernelの定義で保持する。

出典：https://arxiv.org/html/2209.04046v4 （Proposition 4.0.10 の証明）。
この層は本論文の代数 D や Paper の長さ構成を import しない。
-/

public section
universe u
namespace SerrePositivity.CLMST.Inputs
open IsLocalRing Section2

/-- 標準混標数基底上で、極大イデアルの冪と非零 g の perfectoid ideal による巡回商は長さ零。
引用は CLMST Proposition 4.0.10 の証明の巡回商の評価であり、
有限生成・一般加群への帰着や almost 同型不変性は引用に含めない。 -/
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
    · by_cases hsmall : h = 1 ∧ ¬ (p : A) ∣ g
      · obtain ⟨rfl, hpg⟩ := hsmall
        exact completedLength_cyclic_fin_one_eq_zero_of_not_dvd A t p ht htp hperf g hpg n
      · sorry

end SerrePositivity.CLMST.Inputs
