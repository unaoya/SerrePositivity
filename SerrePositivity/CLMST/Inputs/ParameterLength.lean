module

public import SerrePositivity.CLMST.StageFiniteness
public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedNormalized
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # CLMST Proposition 4.0.14 の一般段の商の長さ（文献入力）

実際の有限段 `D_n=A_n⊗_A D` の任意のパラメータ系について、
perfectoid 化の商の正規化長さが `p^(-nh)` 倍の Hilbert–Samuel 重複度であると引用する。
重複度を D のものへあらかじめ置き換えず、一般の n と標準写像を保持する。
定義から証明した正規化長さを使い、零段への特殊化と同型不変性は引用に含めない。

出典：https://arxiv.org/html/2209.04046v4 （Proposition 4.0.14）。
同命題の証明自身（Prop 2.4.7、パラメータの変更、補正項の長さ比較）は文献入力に残る。
-/

public section
universe u
namespace SerrePositivity.CLMST.Inputs
open IsLocalRing Section2
open scoped ENNReal

/-- CLMST Proposition 4.0.14：任意の有限段のパラメータ商に対する長さ・重複度の公式。
`stageRank h p n=p^(nh)` の逆数を保ち、商には有限段からの標準 D 代数写像を用いる。 -/
theorem proposition_4_0_14
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
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
    (n : ℕ) (hlocal : IsLocalRing (StageAlgebra A D t p n)) :
    let _ := hlocal
    ∀ (y : Fin h → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      let _ := Module.compHom
        ((RPerfd A D t p hperf) ⧸
          Ideal.span (Set.range fun j ↦ toRPerfd A D t p hperf n (y j)))
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
      (RootTowerLength.completedNormalizedLength A t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
        ((RPerfd A D t p hperf) ⧸
          Ideal.span (Set.range fun j ↦ toRPerfd A D t p hperf n (y j))) =
        ENNReal.ofReal
          (HilbertSamuel.multiplicity (StageAlgebra A D t p n) (Ideal.span (Set.range y))
            (StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ≥0∞) := by
  sorry

end SerrePositivity.CLMST.Inputs
