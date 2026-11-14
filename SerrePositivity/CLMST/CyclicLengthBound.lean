module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Roots
public import SerrePositivity.LengthAlgebra.RootTowerLength.Coordinate
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.CommutativeAlgebra.PrincipalMaximalFactorization
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Powers
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.CommutativeAlgebra.ModPHypersurfaceGrowth
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Graded
public import SerrePositivity.BhattScholze.PerfectoidIdeal.CompletedQuotient
public import SerrePositivity.LengthAlgebra.QuotientBounds
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRoots
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.CommutativeAlgebra.RootTower.StageModPLength
public import SerrePositivity.LengthAlgebra.RootTowerLength.StageDecay
public import SerrePositivity.LengthAlgebra.Almost
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Prop 4.0.10：perfectoid イデアルで消える加群の正規化長さの消滅

## 概要

巡回 perfectoid 商の正規化長さが零であることを、`p` の場合、`p` の冪の単元倍、単元、一元のパラメータ系、`p` で割れない場合（全射性と有限段の Frobenius 比較による一様な正規化上界）に分けて示し（`cyclic_length_eq_zero`）、`p` の因子を除く帰着で一般の `g` へ広げる。一般の加群へ帰着し（`completedLength_eq_zero_of_perfectoidIdeal_annihilates`）、mod pᴺ の almost 同型から長さの一致を導く。

## 方針

根の代表元と商の Frobenius の単射性から根のイデアルの所属を導き、`p` 冪根を加えた商から元の商へのフィルトレーションの評価（倍率 `p^n`）を使う。`p` で割れない場合の全射性は主イデアル商の perfectoid 化の全射性から得る。

## 規約

CLMST Prop 4.0.10。BS Cor 7.3・Thm 7.4 の適用形を名前つきで引用する。旧入口 `Inputs.cyclic_length_eq_zero*`（別名）は削除した。旧 `CLMST/Cyclic*`（9 本）・`RootFiltrationBound`・`NormalizedAlmostLength`・`AlmostLength`・`PerfectoidFrobeniusComparison`。

## 使われ方

Paper（Theorem 2.5 の混標数）、`ParameterQuotientLength`。
-/

@[expose] public noncomputable section

universe u

section CyclicPLengthPart

namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A)

/-- pを座標に含む塔で、perfectoid商の被約性があればpの場合の巡回長さ評価を得る。 -/
theorem completedLength_cyclic_p_eq_zero_of_reduced
    (i : Fin h) (hti : t i = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (hred : IsReduced (BhattScholze.perfectoidQuotient (CompletedTower A t p) p hperf
      (p : CompletedTower A t p))) (n : ℕ) :
    (RootTowerLength.completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p))) = 0 := by
  have hp : (p : A) ∈ maximalIdeal A := hti ▸ ht i
  have hIK : ((maximalIdeal A) ^ n).map (algebraMap A (CompletedTower A t p)) ≤
      (completedTowerMaxIdeal A t p) ^ n ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) := by
    rw [Ideal.map_pow]
    exact le_sup_left
  exact RootTowerLength.completedNormalizedLength_quotient_eq_zero_of_coordinate_roots
    A t p ht hp ((maximalIdeal A) ^ n)
    (RootTowerLength.finiteLength_quotient_maximalIdeal_pow A n) n le_rfl _ hIK i
    (fun m ↦ (le_sup_right : _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (p : CompletedTower A t p) ≤ _) (BhattScholze.completedTowerRoot_mem_perfectoidIdeal_p_of_reduced
        A t p hperf hred m i hti))

/-- 標数pのperfectoid商の被約性を定義から供給し、pの場合の全巡回評価を得る。 -/
theorem completedLength_cyclic_p_eq_zero
    (i : Fin h) (hti : t i = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (n : ℕ) :
    (RootTowerLength.completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p))) = 0 :=
  completedLength_cyclic_p_eq_zero_of_reduced A t p ht i hti hperf
    (BhattScholze.perfectoidQuotient_p_isReduced (CompletedTower A t p) p hperf) n

end SerrePositivity.CLMST

end CyclicPLengthPart

section CyclicUnitLengthPart

namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2 _root_.SerrePositivity.RootTowerLength

/-- 単元gの巡回商は、基底極大イデアルの任意の冪に対して長さ零。 -/
theorem completedLength_cyclic_unit_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : IsUnit g) (n : ℕ) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  have hI := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_eq_top_of_isUnit (CompletedTower A t p) p hperf
    (algebraMap A (CompletedTower A t p) g) (hg.map (algebraMap A (CompletedTower A t p)))
  have htop : (completedTowerMaxIdeal A t p) ^ n ⊔
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) =
      ⊤ := by rw [hI, sup_top_eq]
  let : Subsingleton (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) :=
    Ideal.Quotient.subsingleton_iff.mpr htop
  exact (completedNormalizedLength A t p ht).len_eq_zero_of_subsingleton _

end SerrePositivity.CLMST

end CyclicUnitLengthPart

section CyclicFactorReductionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2 _root_.SerrePositivity.RootTowerLength

/-- 非零gからpの因子を有限回取り除ける。正則局所性やWitt表示は不要。 -/
theorem exists_p_power_factor_of_nonzero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (p : ℕ) (hp : (p : A) ∈ maximalIdeal A) (g : A) (hg : g ≠ 0) :
    ∃ c : ℕ, ∃ g' : A, g = (p : A) ^ c * g' ∧ ¬ (p : A) ∣ g' :=
  exists_pow_mul_not_dvd (p : A) g hp hg

/-- 一元パラメータ系がpなら、非零元はpの冪と単元の積。 -/
theorem exists_p_power_unit_of_fin_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (t : Fin 1 → A) (p : ℕ)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (g : A) (hg : g ≠ 0) :
    ∃ c : ℕ, ∃ g' : A, g = (p : A) ^ c * g' ∧ IsUnit g' := by
  have hp := span_parameter_fin_one t ht
  rw [htp] at hp
  exact exists_pow_mul_unit_of_principal_maximalIdeal (p : A) g hp hg

section Comparison
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g g' : A) (c : ℕ) (hg : g = (p : A) ^ c * g')

include c hg

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- p因子を取り除くと、元のperfectoidイデアルは残りのイデアルに含まれる。 -/
theorem perfectoidIdeal_le_of_p_power_factor :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) ≤
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g') := by
  apply _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mono
  apply Ideal.span_singleton_le_span_singleton.mpr
  refine ⟨algebraMap A (CompletedTower A t p) ((p : A) ^ c), ?_⟩
  rw [hg, map_mul, mul_comm]

end Comparison
end SerrePositivity.CLMST

end CyclicFactorReductionPart

section CyclicPPowerLengthPart

namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2 _root_.SerrePositivity.RootTowerLength

/-- pの冪の単元倍の場合、任意の冪の巡回長さは零。 -/
theorem completedLength_cyclic_p_power_unit_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (i : Fin h) (hti : t i = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g a : A) (c : ℕ) (hg : g = (p : A) ^ c * a) (ha : IsUnit a) (n : ℕ) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      ((completedTowerMaxIdeal A t p) ^ n ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  by_cases hc : c = 0
  · subst c
    have hga : g = a := by simpa only [pow_zero, one_mul] using hg
    exact completedLength_cyclic_unit_eq_zero A t p ht hperf g (hga ▸ ha) n
  · have hI : _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g) =
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) := by
      rw [hg, map_mul, map_pow, map_natCast,
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mul_unit_eq _ p hperf _ _ (ha.map (algebraMap A (CompletedTower A t p))),
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_p_pow_eq _ p hperf c (Nat.pos_of_ne_zero hc)]
    have heq := congrArg (fun I : Ideal (CompletedTower A t p) ↦
      (completedTowerMaxIdeal A t p) ^ n ⊔ I) hI
    exact ((completedNormalizedLength A t p ht).len_congr _ _
      (Ideal.quotientEquivAlgOfEq (CompletedTower A t p) heq).toLinearEquiv).trans
        (completedLength_cyclic_p_eq_zero A t p ht i hti hperf n)

/-- 一元パラメータ系では、全ての非零gに対して巡回長さ零が成立する。 -/
theorem completedLength_cyclic_fin_one_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (t : Fin 1 → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : g ≠ 0) (n : ℕ) :
    (completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  obtain ⟨c, a, hga, ha⟩ := exists_p_power_unit_of_fin_one A t p ht htp g hg
  exact completedLength_cyclic_p_power_unit_eq_zero A t p _ 0 htp hperf g a c hga ha n

end SerrePositivity.CLMST

end CyclicPPowerLengthPart

section CyclicTorsionComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2 _root_.SerrePositivity.RootTowerLength

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
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      ((completedTowerMaxIdeal A t p) ^ a ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g'))) := by
  let C := CompletedTower A t p
  let : Algebra.FinitePresentation C (C ⧸ Ideal.span {algebraMap A C g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton (algebraMap A C g))
  let S := BhattScholze.perfectoidQuotient C p hperf (algebraMap A C g)
  let κ : C →+* S := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization C (Ideal.span {algebraMap A C g}) p hperf).comp
    (Ideal.Quotient.mk (Ideal.span {algebraMap A C g}))
  have hS : IsIntegralPerfectoid S p :=
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization C (Ideal.span {algebraMap A C g}) p hperf).1
  have hQ : IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p :=
    hS.pTorsionQuotient_isIntegralPerfectoid S p
  have hgzero : (p : S) ^ c * κ (algebraMap A C g') = 0 := by
    have hh := (_root_.SerrePositivity.BhattScholze.Almost.span_le_perfectoidIdeal C p hperf (algebraMap A C g))
      (Ideal.subset_span (Set.mem_singleton _))
    change κ (algebraMap A C g) = 0 at hh
    simpa only [hg, map_mul, map_pow, map_natCast] using hh
  apply completedNormalizedLength_quotient_pow_eq_of_coordinateRoot_mul A t p ht
    (hti ▸ ht i) i _ _ (perfectoidIdeal_le_of_p_power_factor A t p hperf g g' c hg) _ a
  intro n b hb
  have hpb : (p : S) * κ b = 0 :=
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid C S p
      hperf hS hQ κ (algebraMap A C g') c hgzero b hb
  have hρ : κ (Section2.completedTowerRoot A t p n i) ^ (p ^ n) = (p : S) := by
    rw [← map_pow, Section2.completedTowerRoot_pow, hti, map_natCast, map_natCast]
  change κ (Section2.completedTowerRoot A t p n i * b) = 0
  rw [map_mul]
  exact hS.p_power_root_mul_eq_zero_of_pow_mul_eq_zero S p _ n hρ 1 (κ b)
    (by simpa only [pow_one] using hpb)

end SerrePositivity.CLMST

end CyclicTorsionComparisonPart

section CyclicPerfectoidizationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2

theorem completedTowerCyclicQuotient_p_regular_and_complete
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hpg : ¬ (p : A) ∣ g) :
    let Q := CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}
    IsSMulRegular Q (p : Q) ∧ IsAdicComplete (Ideal.span {(p : Q)}) Q := by
  let C := CompletedTower A t p
  let := flat_completedTower_over_base A t p
  have ha : IsSMulRegular A (p : A) := by
    rw [← htp]
    exact HilbertSamuel.isSMulRegular_generator_of_span_eq_maximalIdeal A t ht hdim 0
  let B := A ⧸ Ideal.span {(p : A)}
  let : IsDomain B := modP_isDomain_of_parameters A t p ht htp hdim
  have hgA : IsSMulRegular B (Ideal.Quotient.mk (Ideal.span {(p : A)}) g) := by
    apply IsSMulRegular.of_ne_zero
    intro hz
    exact hpg (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hgC' := isSMulRegular_mod_of_flat (S := C) (p : A) g ha hgA
  have hI : Ideal.span {algebraMap A C (p : A)} = Ideal.span {(p : C)} := by
    rw [map_natCast]
  let e := Ideal.quotientEquivAlgOfEq C hI
  have hgCbase : IsSMulRegular (C ⧸ Ideal.span {algebraMap A C (p : A)})
      (algebraMap A C g) :=
    (isSMulRegular_algebraMap_iff (R := C)
      (A := C ⧸ Ideal.span {algebraMap A C (p : A)})).mp hgC'
  have hgC : IsSMulRegular (C ⧸ Ideal.span {(p : C)})
      (Ideal.Quotient.mk (Ideal.span {(p : C)}) (algebraMap A C g)) :=
    (isSMulRegular_algebraMap_iff (R := C) (A := C ⧸ Ideal.span {(p : C)})).mpr
      ((e.toLinearEquiv.isSMulRegular_congr (algebraMap A C g)).mp hgCbase)
  have haC := isSMulRegular_p_completedTower A t p ha
  let : IsAdicComplete (Ideal.span {(p : C)}) C := by
    rcases hperf with hsub | ⟨_, hc, _⟩
    · let : Subsingleton C := hsub
      infer_instance
    · exact hc
  constructor
  · have hh := isSMulRegular_quotient_span_of_regular_mod C
      (p : C) (algebraMap A C g) haC hgC
    have hcast : Ideal.Quotient.mk (Ideal.span {algebraMap A C g}) (p : C) =
        (p : C ⧸ Ideal.span {algebraMap A C g}) :=
      map_natCast (Ideal.Quotient.mk (Ideal.span {algebraMap A C g})) p
    rw [hcast] at hh
    exact hh
  · have hh := isAdicComplete_quotient_span_of_regular_mod C
      (p : C) (algebraMap A C g) haC hgC
    have hcast : Ideal.Quotient.mk (Ideal.span {algebraMap A C g}) (p : C) =
        (p : C ⧸ Ideal.span {algebraMap A C g}) :=
      map_natCast (Ideal.Quotient.mk (Ideal.span {algebraMap A C g})) p
    rw [hcast] at hh
    exact hh

theorem toPerfectoidization_cyclic_surjective_of_not_dvd
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hpg : ¬ (p : A) ∣ g) :
    letI : Algebra.FinitePresentation (CompletedTower A t p)
        (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
      Algebra.FinitePresentation.quotient
        (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
    Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf) := by
  exact BhattScholze.perfectoidIdeal_quotientMap_surjective (CompletedTower A t p) p hperf
    (algebraMap A (CompletedTower A t p) g)

end SerrePositivity.CLMST

end CyclicPerfectoidizationPart

section RootFiltrationBoundPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.SerrePositivity.RootTowerLength
open scoped _root_.ENNReal

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A)

/-- pを含む基底極大イデアルの拡大で消える商は、pのp^n乗根を追加した商のp^n倍以下。 -/
theorem completedLength_quotient_le_root_factor
    (K : Ideal (CompletedTower A t p)) (hJK : completedTowerMaxIdeal A t p ≤ K)
    (i : Fin h) (hti : t i = (p : A)) (n : ℕ) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n * (completedNormalizedLength A t p ht).len
        (CompletedTower A t p ⧸ (K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i})) := by
  have hpK : (p : CompletedTower A t p) ∈ K := by
    apply hJK
    have hpA : (p : A) ∈ maximalIdeal A := hti ▸ ht i
    simpa only [completedTowerMaxIdeal, map_natCast] using Ideal.mem_map_of_mem
      (algebraMap A (CompletedTower A t p)) hpA
  have hroot : Section2.completedTowerRoot A t p n i ^ (p ^ n) ∈ K := by
    simpa only [Section2.completedTowerRoot_pow, hti, map_natCast] using hpK
  simpa only [pow_one, Nat.cast_pow] using
    (completedNormalizedLength A t p ht).len_quotient_le_mul_of_pow_mem
      K 1 (by simpa only [pow_one] using hJK) (Section2.completedTowerRoot A t p n i) (p ^ n) hroot

/-- 任意の有限段の有限長な商で、根を追加した商を覆えば、元の商の数値上界が得られる。
根の指数nと評価する段mの分母を混同しない。 -/
theorem completedLength_quotient_le_root_factor_stage_length
    (hp : (p : A) ∈ maximalIdeal A) (K : Ideal (CompletedTower A t p))
    (hJK : completedTowerMaxIdeal A t p ≤ K) (i : Fin h) (hti : t i = (p : A))
    (n m : ℕ) (H : Ideal (TowerStage A t p m))
    (hfinite : IsFiniteLength (TowerStage A t p m) (TowerStage A t p m ⧸ H))
    (hJH : completedTowerMaxIdeal A t p ≤
      H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)))
    (hHK : H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) ≤
      K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i}) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m) (TowerStage A t p m ⧸ H) : ℝ≥0∞) /
          (stageRank h p m : ℝ≥0∞)) := by
  refine (completedLength_quotient_le_root_factor A t p ht K hJK i hti n).trans ?_
  have hb := (completedNormalizedLength A t p ht).len_quotient_le_of_pow_le
    1 _ _ (by simpa only [pow_one] using hJH) hHK
  rw [completedNormalizedLength_quotient_eq_length A t p ht hp m H hfinite] at hb
  exact mul_le_mul_right hb _

include ht in
/-- 有限段で基底極大イデアルを含む関係式による商は有限長。
完備塔のイデアルを縮約した商にも使うため、有限長性を仮定として残さない。 -/
theorem isFiniteLength_stage_quotient_of_maximalIdeal_map_le
    (m : ℕ) (H : Ideal (TowerStage A t p m))
    (hH : (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ≤ H) :
    IsFiniteLength (TowerStage A t p m) (TowerStage A t p m ⧸ H) := by
  let B := TowerStage A t p m
  let Q := B ⧸ H
  let : IsLocalRing B := isLocalRing_towerStage A t p ht m
  let : Module.Finite A B := towerStage_finite A t p m
  let : (maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have hann : maximalIdeal A ≤ Module.annihilator A Q := by
    intro a ha
    apply Module.mem_annihilator.mpr
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    change a • (Ideal.Quotient.mkₐ A H).toLinearMap b = 0
    rw [← (Ideal.Quotient.mkₐ A H).toLinearMap.map_smul]
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk H (algebraMap A B a * b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (H.mul_mem_right _ (hH (Ideal.mem_map_of_mem _ ha)))
  have hfin : IsFiniteLength A Q := isFiniteLength_of_le_radical_annihilator
    (maximalIdeal A) Q (hann.trans Ideal.le_radical)
  apply Module.length_ne_top_iff.mp
  rw [← length_eq_of_common_residueField (residue_surjective_towerStage A t p ht m)]
  exact Module.length_ne_top_iff.mpr hfin

/-- 根を追加した完備塔のイデアルの縮約で、原典の最初の二つの不等式を評価する。 -/
theorem completedLength_quotient_le_root_contraction_length
    (K : Ideal (CompletedTower A t p)) (hJK : completedTowerMaxIdeal A t p ≤ K)
    (i : Fin h) (hti : t i = (p : A)) (n m : ℕ) :
    let H := (K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i}).comap
      (algebraMap (TowerStage A t p m) (CompletedTower A t p))
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m) (TowerStage A t p m ⧸ H) : ℝ≥0∞) /
          (stageRank h p m : ℝ≥0∞)) := by
  let H := (K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i}).comap
    (algebraMap (TowerStage A t p m) (CompletedTower A t p))
  have hbase : (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ≤ H := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap (TowerStage A t p m) (CompletedTower A t p)
      (algebraMap A (TowerStage A t p m) a) ∈
        K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i}
    rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p m) (CompletedTower A t p)]
    exact (show K ≤ K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i} from le_sup_left)
      (hJK (Ideal.mem_map_of_mem _ ha))
  have hJH : completedTowerMaxIdeal A t p ≤
      H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) := by
    have hh := Ideal.map_mono (f := algebraMap (TowerStage A t p m) (CompletedTower A t p)) hbase
    simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq, completedTowerMaxIdeal] using hh
  exact completedLength_quotient_le_root_factor_stage_length A t p ht (hti ▸ ht i)
    K hJK i hti n m H (isFiniteLength_stage_quotient_of_maximalIdeal_map_le A t p ht m H hbase)
    hJH (Ideal.map_comap_le)

/-- n段のp冪根と根の代表元zをm段の関係式に加えたイデアル。
m≥nではp冪根の代表は座標のp^(m-n)乗である。 -/
def stageRootRepresentativeIdeal (n m : ℕ) (i : Fin h) (z : TowerStage A t p m) :
    Ideal (TowerStage A t p m) :=
  (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
    Ideal.span {stageX A t p m i ^ (p ^ (m - n))} ⊔ Ideal.span {z}

/-- 根の代表元の所属から、有限段の明示的な商による長さの上界を得る。
残る低次元評価の対象を、この通常長さそのものとして明示する。 -/
theorem completedLength_quotient_le_stage_root_estimate
    (K : Ideal (CompletedTower A t p)) (hJK : completedTowerMaxIdeal A t p ≤ K)
    (i : Fin h) (hti : t i = (p : A)) (n m : ℕ) (hnm : n ≤ m)
    (z : TowerStage A t p m)
    (hz : algebraMap (TowerStage A t p m) (CompletedTower A t p) z ∈
      K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i}) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m)
          (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m i z) : ℝ≥0∞) /
          (stageRank h p m : ℝ≥0∞)) := by
  let H := stageRootRepresentativeIdeal A t p n m i z
  have hbase : (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ≤ H :=
    le_sup_of_le_left le_sup_left
  have hJH : completedTowerMaxIdeal A t p ≤
      H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) := by
    have hh := Ideal.map_mono (f := algebraMap (TowerStage A t p m) (CompletedTower A t p)) hbase
    simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq, completedTowerMaxIdeal] using hh
  have hHK : H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) ≤
      K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i} := by
    dsimp only [H, stageRootRepresentativeIdeal]
    rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow]
    change completedTowerMaxIdeal A t p ⊔
      Ideal.span {Section2.completedTowerRoot A t p m i ^ (p ^ (m - n))} ⊔
        Ideal.span {algebraMap (TowerStage A t p m) (CompletedTower A t p) z} ≤ _
    rw [Section2.completedTowerRoot_pow_of_le A t p n m hnm i]
    exact sup_le (sup_le (hJK.trans le_sup_left) le_sup_right)
      ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  exact completedLength_quotient_le_root_factor_stage_length A t p ht (hti ▸ ht i)
    K hJK i hti n m H (isFiniteLength_stage_quotient_of_maximalIdeal_map_le A t p ht m H hbase)
    hJH hHK

omit [IsNoetherianRing A] [Fact p.Prime] in
/-- n段の根をm段の座標の冪で表した商の通常長さは、m段の根を零にした商の
p^(m-n)倍以下。段の差から生じる倍率を正規化前に保持する。 -/
theorem length_stageRootRepresentativeIdeal_le
    (n m : ℕ) (i : Fin h) (z : TowerStage A t p m) :
    Module.length (TowerStage A t p m)
      (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m i z) ≤
        ((p ^ (m - n) : ℕ) : ℕ∞) * Module.length (TowerStage A t p m)
          (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p m m i z) := by
  have hh := length_quotient_sup_span_pow_le (TowerStage A t p m)
    ((maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔ Ideal.span {z})
    (stageX A t p m i) (p ^ (m - n))
  have hn : stageRootRepresentativeIdeal A t p n m i z =
      ((maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔ Ideal.span {z}) ⊔
        Ideal.span {stageX A t p m i ^ (p ^ (m - n))} := sup_right_comm _ _ _
  have hm : stageRootRepresentativeIdeal A t p m m i z =
      ((maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔ Ideal.span {z}) ⊔
        Ideal.span {stageX A t p m i} := by
    dsimp only [stageRootRepresentativeIdeal]
    rw [Nat.sub_self, pow_zero, pow_one]
    exact sup_right_comm _ _ _
  rw [(Ideal.quotientEquivAlgOfEq (TowerStage A t p m) hn).toLinearEquiv.length_eq,
    (Ideal.quotientEquivAlgOfEq (TowerStage A t p m) hm).toLinearEquiv.length_eq]
  exact hh

end SerrePositivity.CLMST

end RootFiltrationBoundPart

section PerfectoidFrobeniusComparisonPart

namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2

/-- 冪写像の反復は、指数を反復した冪写像。 -/
theorem iterate_pow_apply {S : Type u} [Monoid S] (p m : ℕ) (x : S) :
    ((fun y : S ↦ y ^ p)^[m]) x = x ^ (p ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

/-- mod p の Frobenius が全射なら、任意の元の p^m 乗根の代表元を mod p で取れる。 -/
theorem exists_root_mod_p_of_surjective (R : Type u) [CommRing R] (p m : ℕ)
    (hF : Function.Surjective (fun x : R ⧸ Ideal.span {(p : R)} ↦ x ^ p)) (g : R) :
    ∃ x : R, x ^ (p ^ m) - g ∈ Ideal.span {(p : R)} := by
  obtain ⟨x, hx⟩ := hF.iterate m (Ideal.Quotient.mk (Ideal.span {(p : R)}) g)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [iterate_pow_apply, ← map_pow] at hx
  refine ⟨x, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, hx, sub_self]

/-- integral perfectoid の定義に含まれる全射性から根の代表元を取る。
零環の場合も許すが、単射性はこの補題の結論には含めない。 -/
theorem exists_root_mod_p_of_perfectoid (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (m : ℕ) (g : R) :
    ∃ x : R, x ^ (p ^ m) - g ∈ Ideal.span {(p : R)} := by
  rcases hR with hR | ⟨_, _, _, hF, _⟩
  · let : Subsingleton R := hR
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim ((0 : R) ^ (p ^ m) - g) 0]
    exact Ideal.zero_mem _
  · exact exists_root_mod_p_of_surjective R p m hF g

/-- π^(p^m)=p による、実際の商環間の Frobenius 射。
対象の mod p 商が標数 p であることを明示する。 -/
def quotientRootFrobenius (S : Type u) [CommRing S] (p m : ℕ) [Fact p.Prime]
    [CharP (S ⧸ Ideal.span {(p : S)}) p] (π : S) (hπ : π ^ (p ^ m) = (p : S)) :
    S ⧸ Ideal.span {π} →+* S ⧸ Ideal.span {(p : S)} :=
  Ideal.Quotient.lift (Ideal.span {π})
    ((iterateFrobenius (S ⧸ Ideal.span {(p : S)}) p m).comp
      (Ideal.Quotient.mk (Ideal.span {(p : S)}))) (by
        change Ideal.span {π} ≤ RingHom.ker
          ((iterateFrobenius (S ⧸ Ideal.span {(p : S)}) p m).comp
            (Ideal.Quotient.mk (Ideal.span {(p : S)})))
        apply Ideal.span_le.mpr
        intro x hx
        have hxπ : x = π := Set.mem_singleton_iff.mp hx
        rw [hxπ]
        change (iterateFrobenius (S ⧸ Ideal.span {(p : S)}) p m)
          (Ideal.Quotient.mk (Ideal.span {(p : S)}) π) = 0
        rw [iterateFrobenius_def, ← map_pow, hπ]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

@[simp] theorem quotientRootFrobenius_mk (S : Type u) [CommRing S] (p m : ℕ) [Fact p.Prime]
    [CharP (S ⧸ Ideal.span {(p : S)}) p] (π : S) (hπ : π ^ (p ^ m) = (p : S)) (x : S) :
    quotientRootFrobenius S p m π hπ (Ideal.Quotient.mk (Ideal.span {π}) x) =
      Ideal.Quotient.mk (Ideal.span {(p : S)}) (x ^ (p ^ m)) := by
  simp [quotientRootFrobenius, iterateFrobenius_def]

/-- 原典式 (4.0.10.1) の図式追跡。
根の代表元と、R/I 上の実際の商 Frobenius 射の単射性から所属が従う。
R/I の perfectoid 性やその単射性を未知の一般構造に隠さない。 -/
theorem root_mem_sup_of_quotient_frobenius_injective
    (R : Type u) [CommRing R] (p m : ℕ) [Fact p.Prime] (I : Ideal R)
    [CharP ((R ⧸ I) ⧸ Ideal.span {(p : R ⧸ I)}) p]
    (π : R) (hπ : π ^ (p ^ m) = (p : R))
    (hF : Function.Injective (quotientRootFrobenius (R ⧸ I) p m
      (Ideal.Quotient.mk I π) (by rw [← map_pow, hπ]; exact map_natCast _ _)))
    (g x : R) (hg : g ∈ I) (hx : x ^ (p ^ m) - g ∈ Ideal.span {(p : R)}) :
    x ∈ Ideal.span {π} ⊔ I := by
  let f := Ideal.Quotient.mk I
  have hx' : f (x ^ (p ^ m)) ∈ Ideal.span {(p : R ⧸ I)} := by
    have hmap := Ideal.mem_map_of_mem f hx
    rw [Ideal.map_span, Set.image_singleton, map_natCast] at hmap
    have hg0 : f g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hg
    simpa only [map_sub, hg0, sub_zero] using hmap
  have hzero : Ideal.Quotient.mk (Ideal.span {f π}) (f x) = 0 := by
    apply hF
    rw [quotientRootFrobenius_mk, map_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [map_pow] using hx'
  have hmem : f x ∈ (Ideal.span {π}).map f := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hpre := hmem
  change x ∈ Ideal.comap f ((Ideal.span {π}).map f) at hpre
  rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective] at hpre
  change x ∈ Ideal.span {π} ⊔ RingHom.ker f at hpre
  rw [Ideal.mk_ker] at hpre
  exact hpre

/-- 実際の整perfectoid環と互換的なp冪根では、商の反復Frobeniusの単射性を四条件から供給できる。
零環は別に処理するため、pの非可逆性を明示する。 -/
theorem quotientRootFrobenius_injective_of_integralPerfectoid
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : S))]
    (hS : IsIntegralPerfectoid S p) (ρ : ℕ → S) (hρ₀ : ρ 0 = (p : S))
    (hρ : ∀ m, ρ (m + 1) ^ p = ρ m) (n : ℕ) :
    Function.Injective (quotientRootFrobenius S p n (ρ n)
      (by simpa only [zero_add, hρ₀] using compatibleRoots_pow p ρ hρ 0 n)) := by
  let hpRoot : ρ n ^ (p ^ n) = (p : S) := by
    simpa only [zero_add, hρ₀] using compatibleRoots_pow p ρ hρ 0 n
  let F := quotientRootFrobenius S p n (ρ n) hpRoot
  intro x y hxy
  have hz : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hrep⟩ := Ideal.Quotient.mk_surjective (x - y)
  rw [← hrep, quotientRootFrobenius_mk] at hz
  have hmem : z ^ (p ^ n) ∈ Ideal.span {(p : S)} := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hroot := (hS.pow_kernel_of_compatible_roots S p ρ hρ₀ hρ n z).mp hmem
  have hz0 : Ideal.Quotient.mk (Ideal.span {ρ n}) z = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hroot
  exact sub_eq_zero.mp (hrep.symm.trans hz0)

/-- 全射先がperfectoidなら、根の代表元はp冪根と写像の核が生成するイデアルに入る。
零環も含め、全射性によって根の係数を元環へ持ち上げる。 -/
theorem root_mem_sup_of_surjective_perfectoid
    {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (f : R →+* S) (hf : Function.Surjective f) (hS : IsIntegralPerfectoid S p)
    (ρ : ℕ → R) (hρ₀ : ρ 0 = (p : R)) (hρ : ∀ m, ρ (m + 1) ^ p = ρ m)
    (n : ℕ) (g x : R) (hg : f g = 0)
    (hx : x ^ (p ^ n) - g ∈ Ideal.span {(p : R)}) :
    x ∈ Ideal.span {ρ n} ⊔ RingHom.ker f := by
  rcases hS with hsub | hnonzero
  · let : Subsingleton S := hsub
    apply (show RingHom.ker f ≤ Ideal.span {ρ n} ⊔ RingHom.ker f from le_sup_right)
    exact Subsingleton.elim (f x) 0
  · let : Fact (¬ IsUnit (p : S)) := ⟨hnonzero.1⟩
    have hS : IsIntegralPerfectoid S p := Or.inr hnonzero
    have hxS : f x ^ (p ^ n) ∈ Ideal.span {(p : S)} := by
      have hmap := Ideal.mem_map_of_mem f hx
      rw [Ideal.map_span, Set.image_singleton, map_natCast] at hmap
      simpa only [map_sub, map_pow, hg, sub_zero] using hmap
    have hmem := (hS.pow_kernel_of_compatible_roots S p (fun m ↦ f (ρ m))
      (by rw [hρ₀, map_natCast]) (fun m ↦ by rw [← map_pow, hρ m]) n (f x)).mp hxS
    have hmem' : f x ∈ (Ideal.span {ρ n}).map f := by
      simpa only [Ideal.map_span, Set.image_singleton] using hmem
    change x ∈ Ideal.comap f ((Ideal.span {ρ n}).map f) at hmem'
    rwa [Ideal.comap_map_of_surjective f hf] at hmem'

/-- 選ばれたperfectoid化の標準写像が全射なら、式(4.0.10.1)が従う。
全射性は未供給の原典入力であり、ここでは明示的な仮定として扱う。 -/
theorem root_mem_sup_perfectoidIdeal_of_surjective
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hsurj : letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
      Function.Surjective
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR))
    (ρ : ℕ → R) (hρ₀ : ρ 0 = (p : R)) (hρ : ∀ m, ρ (m + 1) ^ p = ρ m)
    (n : ℕ) (x : R) (hx : x ^ (p ^ n) - g ∈ Ideal.span {(p : R)}) :
    x ∈ Ideal.span {ρ n} ⊔ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let f := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  exact root_mem_sup_of_surjective_perfectoid p f
    (hsurj.comp Ideal.Quotient.mk_surjective)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).1
    ρ hρ₀ hρ n g x
    (by change _root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR
          (Ideal.Quotient.mk (Ideal.span {g}) g) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero])
    hx

/-- pを座標に含む実際の完備塔では、全射性を供給すれば根の代表元と所属を同時に得る。
互換的な根の列は塔の構成から確認する。 -/
theorem exists_completed_root_mem_sup_perfectoidIdeal_of_surjective
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : CompletedTower A t p)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {g}) :=
        Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
      Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {g}) p hperf))
    (i : Fin h) (hti : t i = (p : A)) (n : ℕ) :
    ∃ x : CompletedTower A t p,
      x ^ (p ^ n) - g ∈ Ideal.span {(p : CompletedTower A t p)} ∧
      x ∈ Ideal.span {Section2.completedTowerRoot A t p n i} ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf g := by
  obtain ⟨x, hx⟩ := exists_root_mod_p_of_perfectoid _ p hperf n g
  refine ⟨x, hx, root_mem_sup_perfectoidIdeal_of_surjective _ p hperf g hsurj
    (fun m ↦ Section2.completedTowerRoot A t p m i) ?_
    (fun m ↦ Section2.completedTowerRoot_succ_pow A t p m i) n x hx⟩
  exact (Section2.completedTowerRoot_zero A t p i).trans (by rw [hti, map_natCast])

/-- mod pで等しい代表元は、任意の冪を取ってもmod pで等しい。 -/
theorem pow_sub_mem_of_sub_mem {R : Type u} [CommRing R]
    (I : Ideal R) (x y : R) (k : ℕ) (hxy : x - y ∈ I) : x ^ k - y ^ k ∈ I := by
  have hq : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := Ideal.Quotient.eq.mpr hxy
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_pow, map_pow, hq, sub_self]

/-- 基底環の元のmod pのp冪根は、指定した段以降の有限段で合同式ごと代表できる。
この入口はperfectoid化への全射性を使わない。段の番号はFrobeniusの反復数と区別する。 -/
theorem exists_stage_root_mod_p_of_perfectoid
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A) (n m₀ : ℕ) :
    ∃ (m : ℕ) (_ : m₀ ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} := by
  obtain ⟨x, hx⟩ := exists_root_mod_p_of_perfectoid _ p hperf n
    (algebraMap A (CompletedTower A t p) g)
  obtain ⟨m, hm, z, hz⟩ := exists_completedTower_stage_representative A t p x 1 m₀
  rw [pow_one] at hz
  have hpow := pow_sub_mem_of_sub_mem _ _ _ (p ^ n) hz
  have heq : algebraMap (TowerStage A t p m) (CompletedTower A t p)
      (z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g) ∈
        Ideal.span {(p : CompletedTower A t p)} ^ 1 := by
    rw [pow_one, map_sub, map_pow,
      ← IsScalarTower.algebraMap_apply A (TowerStage A t p m) (CompletedTower A t p)]
    simpa only [sub_add_sub_cancel] using (Ideal.span {(p : CompletedTower A t p)}).add_mem hpow hx
  obtain ⟨l, hml, hl⟩ := exists_towerMap_mem_p_pow_of_completed A t p m 1 _ heq
  refine ⟨l, hm.trans hml, towerMap A t p m l hml z, ?_⟩
  simpa only [pow_one, map_sub, map_pow, AlgHom.commutes] using hl

/-- 有限段の根の合同式と、完備塔での式(4.0.10.1)の所属を同じ代表元で得る。
根の指数nと有限段mは区別し、mをnおよび指定した段以降に取る。 -/
theorem exists_stage_root_mem_sup_perfectoidIdeal_of_surjective
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))
    (i : Fin h) (hti : t i = (p : A)) (n m₀ : ℕ) :
    ∃ (m : ℕ) (_ : m₀ ≤ m) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} ∧
      algebraMap (TowerStage A t p m) (CompletedTower A t p) z ∈
        Ideal.span {Section2.completedTowerRoot A t p n i} ⊔
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) := by
  obtain ⟨m, hm, z, hz⟩ := exists_stage_root_mod_p_of_perfectoid A t p hperf g n (max m₀ n)
  refine ⟨m, (le_max_left _ _).trans hm, (le_max_right _ _).trans hm, z, hz, ?_⟩
  have hmap := Ideal.mem_map_of_mem
    (algebraMap (TowerStage A t p m) (CompletedTower A t p)) hz
  rw [Ideal.map_span, Set.image_singleton, map_natCast, map_sub, map_pow,
    ← IsScalarTower.algebraMap_apply A (TowerStage A t p m) (CompletedTower A t p)] at hmap
  exact root_mem_sup_perfectoidIdeal_of_surjective _ p hperf _ hsurj
    (fun l ↦ Section2.completedTowerRoot A t p l i)
    ((Section2.completedTowerRoot_zero A t p i).trans (by rw [hti, map_natCast]))
    (fun l ↦ Section2.completedTowerRoot_succ_pow A t p l i) n _ hmap

/-- perfectoid環で二つのp冪根がmod pで同じ値を持てば、その差は対応するp冪根に属する。
代表元を有限段で選び直す際の曖昧さを、同じ根イデアルの中で制御する。 -/
theorem sub_mem_root_span_of_pow_sub_mem_p
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R) (hρ₀ : ρ 0 = (p : R))
    (hρ : ∀ m, ρ (m + 1) ^ p = ρ m) (n : ℕ) (x y : R)
    (hxy : x ^ (p ^ n) - y ^ (p ^ n) ∈ Ideal.span {(p : R)}) :
    x - y ∈ Ideal.span {ρ n} := by
  rcases hR with hsub | hnonzero
  · let : Subsingleton R := hsub
    rw [Subsingleton.elim (x - y) 0]
    exact Ideal.zero_mem _
  · let : Fact (¬ IsUnit (p : R)) := ⟨hnonzero.1⟩
    have hR : IsIntegralPerfectoid R p := Or.inr hnonzero
    let q := Ideal.Quotient.mk (Ideal.span {(p : R)})
    let F := iterateFrobenius (R ⧸ Ideal.span {(p : R)}) p n
    have hpow : F (q x) = F (q y) := by
      apply sub_eq_zero.mp
      simpa only [q, F, iterateFrobenius_def, map_sub, map_pow] using
        Ideal.Quotient.eq_zero_iff_mem.mpr hxy
    apply (hR.pow_kernel_of_compatible_roots R p ρ hρ₀ hρ n (x - y)).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change F (q (x - y)) = 0
    rw [map_sub, map_sub, hpow, sub_self]

end SerrePositivity.CLMST

end PerfectoidFrobeniusComparisonPart

section CyclicRootEstimatePart

namespace SerrePositivity.CLMST
open _root_.SerrePositivity.Section2 _root_.IsLocalRing _root_.SerrePositivity.RootTowerLength
open scoped _root_.ENNReal

/-- 原典4.0.10の有限段の根と長さ上界までの接続。
全射性は仮定として残し、低次元の成長評価を結論へ埋め込まない。 -/
theorem exists_cyclic_root_stage_length_estimate
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))
    (i : Fin h) (hti : t i = (p : A)) (n m₀ : ℕ) :
    let K := completedTowerMaxIdeal A t p ⊔
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)
    ∃ (m : ℕ) (_ : m₀ ≤ m) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} ∧
      (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
        (p : ℝ≥0∞) ^ n *
          ((Module.length (TowerStage A t p m)
            (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m i z) : ℝ≥0∞) /
              (stageRank h p m : ℝ≥0∞)) := by
  let I := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
    (algebraMap A (CompletedTower A t p) g)
  let K := completedTowerMaxIdeal A t p ⊔ I
  obtain ⟨m, hm, hnm, z, hz, hmem⟩ :=
    exists_stage_root_mem_sup_perfectoidIdeal_of_surjective A t p hperf g hsurj i hti n m₀
  refine ⟨m, hm, hnm, z, hz,
    completedLength_quotient_le_stage_root_estimate A t p ht K le_sup_left i hti n m hnm z ?_⟩
  have hle : Ideal.span {Section2.completedTowerRoot A t p n i} ⊔ I ≤
      K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i} :=
    sup_le le_sup_right (le_sup_of_le_left le_sup_right)
  exact hle hmem

end SerrePositivity.CLMST

end CyclicRootEstimatePart

section CyclicNormalizedBoundPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2 _root_.SerrePositivity.RootTowerLength
open scoped _root_.ENNReal

/-- 有限段の根の代表元による長さ評価を正規化すると、根の指数だけで減少する。 -/
theorem exists_stage_root_normalized_bound
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 2))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (g : A) (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) :
    ∃ c : ℕ, ∀ (n m : ℕ) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} →
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m)
          (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m 0 z) : ℝ≥0∞) /
            (stageRank (r + 2) p m : ℝ≥0∞)) ≤ (c : ℝ≥0∞) / (p : ℝ≥0∞) ^ n := by
  obtain ⟨c, hc⟩ := exists_stage_root_quotient_length_bound A t p ht htp hdim e ι he g hgm hpg
  refine ⟨c, fun n m hnm z hz ↦ ?_⟩
  have hmm : stageRootRepresentativeIdeal A t p m m 0 z =
      (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
        Ideal.span {stageX A t p m 0} ⊔ Ideal.span {z} := by
    simp only [stageRootRepresentativeIdeal, Nat.sub_self, pow_zero, pow_one]
  have hroot : Module.length (TowerStage A t p m)
      (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p m m 0 z) ≤
        ((p ^ (m - n) : ℕ) : ℕ∞) * (((p ^ m : ℕ) : ℕ∞) ^ r * (c : ℕ∞)) := by
    rw [(Ideal.quotientEquivAlgOfEq (TowerStage A t p m) hmm).toLinearEquiv.length_eq]
    exact hc n m hnm z hz
  have hlen := (length_stageRootRepresentativeIdeal_le A t p n m 0 z).trans
    (mul_le_mul_right hroot ((p ^ (m - n) : ℕ) : ℕ∞))
  have hlen' : (Module.length (TowerStage A t p m)
      (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m 0 z) : ℝ≥0∞) ≤
        (p : ℝ≥0∞) ^ (m - n) *
          ((p : ℝ≥0∞) ^ (m - n) * (((p : ℝ≥0∞) ^ m) ^ r * (c : ℝ≥0∞))) := by
    exact_mod_cast hlen
  exact (mul_le_mul_right (ENNReal.div_le_div_right hlen' _) _).trans_eq
    (root_stage_normalization p (Fact.out : p.Prime).ne_zero r n m hnm c)

section Perfectoid
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (htmem : ∀ i, t i ∈ maximalIdeal A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 2))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))

include ht htp hdim e ι he hgm hpg hsurj

/-- 根を取る段の選択に依存しない、完備巡回商のc/p^n上界。
perfectoid化への全射性は明示的な適用条件として残る。 -/
theorem exists_completed_cyclic_div_pow_bound_of_surjective :
    let K := completedTowerMaxIdeal A t p ⊔
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)
    ∃ c : ℕ, ∀ n : ℕ,
      (completedNormalizedLength A t p htmem).len (CompletedTower A t p ⧸ K) ≤
        (c : ℝ≥0∞) / (p : ℝ≥0∞) ^ n := by
  obtain ⟨c, hc⟩ := exists_stage_root_normalized_bound A t p ht htp hdim e ι he g hgm hpg
  refine ⟨c, fun n ↦ ?_⟩
  obtain ⟨m, _, hnm, z, hz, hlen⟩ :=
    exists_cyclic_root_stage_length_estimate A t p htmem hperf g hsurj 0 htp n 0
  exact hlen.trans (hc n m hnm z hz)

/-- pがgを割らない非単元の場合、全射性から一次の巡回商の長さ零を導く。 -/
theorem completedLength_cyclic_first_eq_zero_of_surjective :
    (completedNormalizedLength A t p htmem).len
      (CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  obtain ⟨c, hc⟩ := exists_completed_cyclic_div_pow_bound_of_surjective
    A t p htmem ht htp hdim e ι he hperf g hgm hpg hsurj
  exact ennreal_eq_zero_of_div_pow_bound _ c p (by simp)
    (by exact_mod_cast (Fact.out : p.Prime).one_lt) hc

/-- 同じ条件で、基底極大イデアルの全ての冪に対する巡回商の長さが零。 -/
theorem completedLength_cyclic_pow_eq_zero_of_surjective (a : ℕ) :
    (completedNormalizedLength A t p htmem).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ a ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  apply LengthAlgebra.cyclic_quotient_pow_length_eq_zero_of_first
    (completedNormalizedLength A t p htmem)
  · exact (maximalIdeal A).fg_of_isNoetherianRing.map _
  · exact completedLength_cyclic_first_eq_zero_of_surjective
      A t p htmem ht htp hdim e ι he hperf g hgm hpg hsurj

end Perfectoid

/-- 標準Witt冪級数表示から、pを因子に持たない非単元の巡回評価へ直接接続する。
全射性の確認とdim(A)≤1の場合、およびp因子の処理はこの主張に含めない。 -/
theorem completedLength_cyclic_pow_eq_zero_of_witt_of_surjective
    (A k : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing k]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    (e : A ≃+* MvPowerSeries {i : Fin (r + 2) // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))
    (a : ℕ) :
    (completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ a ⊔
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  let σ := {i : Fin (r + 2) // (i : ℕ) ≠ 0}
  let eQ := wittPresentedModPEquiv A σ k p e
  have heQ : ∀ i : σ,
      eQ (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t i.val)) = MvPowerSeries.X i :=
    fun i ↦ wittPresentedModPEquiv_coordinate A σ k p e (t i.val) i (he i.val i.property)
  exact completedLength_cyclic_pow_eq_zero_of_surjective A t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) ht htp hdim
    eQ Subtype.val heQ hperf g hgm hpg hsurj a

end SerrePositivity.CLMST

end CyclicNormalizedBoundPart

section CyclicLengthPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2

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
        _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
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
          _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
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

end CyclicLengthPart

section AlmostLengthPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (J : Ideal R)
    (lam : NormalizedLength R J)

/-- perfectoid ideal の零化が長さ零を与えるなら、mod p^N で almost 同型な対象の長さは一致。
元の perfectoid ideal の冪等性は仮定せず、mod p^N の像イデアルだけに要求する。 -/
theorem length_eq_of_perfectoid_mod_almost_iso (N : ℕ)
    [Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)]
    (hzero : ∀ X : PowTorsionModule J,
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) X.obj → lam.len X.obj = 0)
    {M M' : PowTorsionModule (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))}
    (e : (Almost.torsionLocalization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)
      (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))).obj M ≅
      (Almost.torsionLocalization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)
        (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))).obj M') :
    (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M.obj =
      (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M'.obj :=
  LengthAlgebra.length_eq_of_almost_iso_baseChange (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) J lam
    Ideal.Quotient.mk_surjective hzero e

/-- mod p^N の全加群の almost 圏での同型から、元の正規化長さの一致を得る。
冪ねじれ部分圏への同型の移送を使い、原典の同型の範囲を保つ。 -/
theorem length_eq_of_perfectoid_mod_full_almost_iso (N : ℕ)
    [Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)]
    (hzero : ∀ X : PowTorsionModule J,
      Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) X.obj → lam.len X.obj = 0)
    {M M' : PowTorsionModule (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))}
    (e : (Almost.localization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)).obj M.obj ≅
      (Almost.localization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)).obj M'.obj) :
    (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M.obj =
      (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M'.obj :=
  LengthAlgebra.length_eq_of_full_almost_iso_baseChange (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) J lam
    Ideal.Quotient.mk_surjective hzero e

end SerrePositivity.CLMST

end AlmostLengthPart

section NormalizedAlmostLengthPart

namespace SerrePositivity.CLMST
open _root_.IsLocalRing _root_.SerrePositivity.Section2 _root_.CategoryTheory

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
      (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
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
  apply _root_.SerrePositivity.BhattScholze.Almost.exists_common_p_pow_annihilates (CompletedTower A t p) p
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
    ((_root_.SerrePositivity.BhattScholze.Almost.perfectoidAlmostModLocalization (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N).obj
        (ModuleCat.of ((CompletedTower A t p) ⧸ Ideal.span {(p : CompletedTower A t p) ^ N}) M) ≅
      (_root_.SerrePositivity.BhattScholze.Almost.perfectoidAlmostModLocalization (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g) N).obj
          (ModuleCat.of
            ((CompletedTower A t p) ⧸ Ideal.span {(p : CompletedTower A t p) ^ N}) M')) →
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len M =
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len M' := by
  let : Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N *
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N =
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g) N) :=
    ⟨_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent _ p hperf _ N⟩
  apply LengthAlgebra.length_eq_of_quotient_almost_iso
    (Ideal.span {(p : CompletedTower A t p) ^ N})
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))
    (completedTowerMaxIdeal A t p)
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))) _ M M' hM hM' hNM hNM'
  intro X hX
  exact completedLength_eq_zero_of_perfectoidIdeal_annihilates
    A k p t hpos htp ht hdim e he hperf g hg X.obj X.property hX

end SerrePositivity.CLMST

end NormalizedAlmostLengthPart
