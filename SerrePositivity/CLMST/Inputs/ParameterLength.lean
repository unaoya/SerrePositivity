module

public import SerrePositivity.CLMST.StageLocality
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import SerrePositivity.CLMST.SourceEulerEvaluation
public import SerrePositivity.CLMST.ParameterFormulaDescent

/-! # CLMST Proposition 4.0.14 の一般段の商の長さ（証明済みの互換入口）

実際の有限段 `D_n=A_n⊗_A D` の任意のパラメータ系について、
perfectoid 化の商の正規化長さが `p^(-nh)` 倍の Hilbert–Samuel 重複度であることを証明する。
重複度を D のものへあらかじめ置き換えず、一般の n と標準写像を保持する。
共通の Euler・錐の理論、実際の平坦基底変更、完備化前後の長さ比較を使う。

出典：https://arxiv.org/html/2209.04046v4 （Proposition 4.0.14）。
依存する文献入力は Bhatt–Scholze の perfectoid 化の存在、CLMST Prop 2.4.7、
Cor 4.0.4、および巡回評価で使うBSの全射性。Prop 4.0.10はこれらから証明済み。
パラメータの変更、余核のEuler消去、数値評価も証明済み。
`Inputs` 名前空間と宣言名は既存利用先の互換性のために保つ。
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
    (n : ℕ) :
    let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
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
  let := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  dsimp only
  intro y hy
  have htA : ∀ i, t i ∈ maximalIdeal A :=
    fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp]
    exact htA _
  have htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D := by
    intro i
    rw [← hsop.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  exact completedTower_stage_parameter_quotient_length_of_source_euler_formula
    A D hinj hres t hdimA hdimD hpos ht hsop p htp e he hperf n (by
      dsimp only
      intro v hv
      exact completedTensor_stage_source_euler_eq_multiplicity
        A D t p htA hp htD hres n v hv) y hy

end SerrePositivity.CLMST.Inputs
