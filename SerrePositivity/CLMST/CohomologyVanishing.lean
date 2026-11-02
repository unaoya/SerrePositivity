module

public import SerrePositivity.CLMST.Inputs.CohomologyVanishing
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite
public import SerrePositivity.CLMST.StageRPerfd

/-! # CLMST の固定 g の消滅からパラメータ系の消滅への接続

非零元 g は有限エタール性の証明から選ぶ。
Corollary 4.0.4 の全段の Koszul 成分を段ゼロへ適用し、
段ゼロの同型・有限単射代数構造とパラメータの移送を使って D のパラメータ系へ戻す。
存在・作用・特殊化は文献入力に相対的な証明であり、新しい sorry は置かない。
-/

@[expose] public section
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2

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
/-- 一つの固定したエタール開集合の元から、D の全パラメータ系に対する Koszul 消滅を導く。 -/
theorem parameter_koszul_annihilates_of_etale (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℕ) (hi : 0 < i) :
    let _ := Module.compHom
      (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i)
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) ≤
        Module.annihilator (CompletedTower A t p)
          (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i) := by
  let : IsLocalRing (Section2.StageAlgebra A D t p 0) := Section2.stage0IsLocalRing A D t p
  let : Module.Finite D (Section2.StageAlgebra A D t p 0) := Section2.stage0ModuleFinite A D t p
  have hz0 := hz.map_finite (Section2.StageAlgebra A D t p 0)
    (Section2.stage0_algebraMap_injective A D t p)
  have hvan := (Inputs.corollary_4_0_4 A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf g hg hEtale).2 0 (algebraMap D _ ∘ z) hz0 i hi
  have hseq : (fun j ↦ toRPerfd A D t p hperf 0
      ((algebraMap D (Section2.StageAlgebra A D t p 0) ∘ z) j)) =
      (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) := by
    funext j
    exact toRPerfd_algebraMap_D A D t p hperf 0 (z j)
  rw [hseq] at hvan
  exact hvan

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 有限エタール化で g を選び、Corollary 4.0.4 を全パラメータ系へ同時に適用する。
非零元の存在そのものは、文献の消滅引用の結論に含めない。 -/
theorem exists_perfectoidIdeal_annihilates_koszul :
    ∃ g : A, g ≠ 0 ∧ ∀ (z : Fin h → D), IsSystemOfParameters D z →
      ∀ i : ℕ, 0 < i →
        let _ := Module.compHom
          (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i)
          (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
        perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g) ≤
            Module.annihilator (CompletedTower A t p)
              (koszulHomologySelf (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) i) := by
  obtain ⟨g, hg, _, hEtale⟩ := exists_finite_etale_away A D hinj
  refine ⟨g, hg, fun z hz i hi ↦ ?_⟩
  exact parameter_koszul_annihilates_of_etale A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf g hg hEtale z hz i hi

end SerrePositivity.CLMST
