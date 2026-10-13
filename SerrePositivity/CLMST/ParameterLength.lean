module

public import SerrePositivity.CLMST.Inputs.ParameterLength
public import SerrePositivity.CommutativeAlgebra.HilbertSamuelEquiv
public import SerrePositivity.CommutativeAlgebra.FiniteParameters
public import SerrePositivity.CommutativeAlgebra.MultiplicityFormulas

/-! # 一般段のパラメータ商の長さから零段と階数の公式へ

CLMST Proposition 4.0.14 の一般 n の公式を、実際の零段のパラメータ系へ適用する。
零段の同型に沿って Samuel 関数・重複度を移し、係数 p^(-0h)=1 を計算する。
正則基底の階数についての特別な公式は、一般の重複度の階数公式から導く。
この接続に直接の sorry や、零段専用の追加引用は置かない。
-/

@[expose] public section
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2
open scoped ENNReal

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
/-- D のパラメータ系を任意の有限段へ移し、同じ商の長さをその段の重複度で評価する。
有限段の局所性やパラメータの移送を利用者に仮定として要求しない。 -/
theorem parameter_quotient_length_at_stage (n : ℕ)
    (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j))) =
      ENNReal.ofReal
        (HilbertSamuel.multiplicity (StageAlgebra A D t p n)
          (Ideal.span (Set.range (algebraMap D (StageAlgebra A D t p n) ∘ z)))
          (StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ≥0∞) := by
  have hzN := isSystemOfParameters_stageAlgebra A D t p hsop n z hz
  have hlen := Inputs.proposition_4_0_14 A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf n (algebraMap D _ ∘ z) hzN
  have hseq : (fun j ↦ toRPerfd A D t p hperf n
      ((algebraMap D (StageAlgebra A D t p n) ∘ z) j)) =
      (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) := by
    funext j
    exact toRPerfd_algebraMap_D A D t p hperf n (z j)
  rw [hseq] at hlen
  exact hlen

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 一般段の公式を零段へ適用し、D のパラメータ商の長さを重複度に同定する。 -/
theorem parameter_quotient_length
    (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j))) =
      ENNReal.ofReal (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
  have hlen := parameter_quotient_length_at_stage A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf 0 z hz
  have hsymm : (⇑(stage0Equiv A D t p).symm.toRingEquiv : D → StageAlgebra A D t p 0) =
      algebraMap D (StageAlgebra A D t p 0) := by
    funext d
    apply (stage0Equiv A D t p).injective
    simp
  have hm := HilbertSamuel.multiplicity_span_map_ringEquiv
    (stage0Equiv A D t p).symm.toRingEquiv z
  rw [hsymm] at hm
  rw [hm] at hlen
  simpa only [stageRank, Nat.zero_mul, pow_zero, Nat.cast_one, div_one] using hlen

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- Prop 4.0.14 の「特に」の階数公式は、零段の商比較と証明済みの重複度公式から従う。 -/
theorem base_parameter_quotient_length_eq_rank :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j))))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j)))) =
      (Module.finrank A D : ℝ≥0∞) := by
  have hlen := parameter_quotient_length A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf (algebraMap A D ∘ t) hsop
  rw [HilbertSamuel.multiplicity_eq_rank_of_regular_base A D hinj hres t ht hdimA hsop] at hlen
  simpa only [Function.comp_apply, Rat.cast_natCast, ENNReal.ofReal_natCast] using hlen

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 原典の特別な公式を、m_A を C に拡大したイデアルによる商そのもので述べる。 -/
theorem base_maximalIdeal_quotient_length_eq_rank :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        (maximalIdeal A).map (algebraMap A (RPerfd A D t p hperf)))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        (maximalIdeal A).map (algebraMap A (RPerfd A D t p hperf))) =
      (Module.finrank A D : ℝ≥0∞) := by
  have hs : algebraMap A (RPerfd A D t p hperf) ∘ t =
      (fun j ↦ algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j))) := by
    funext j
    exact IsScalarTower.algebraMap_apply A D (RPerfd A D t p hperf) (t j)
  have hI : (maximalIdeal A).map (algebraMap A (RPerfd A D t p hperf)) =
      Ideal.span (Set.range fun j ↦
        algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j))) := by
    rw [← ht, Ideal.map_span, ← Set.range_comp, hs]
  rw [hI]
  exact base_parameter_quotient_length_eq_rank A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf

end SerrePositivity.CLMST
