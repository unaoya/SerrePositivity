module

public import SerrePositivity.Paper.Section2.PerfectKoszulLength
public import SerrePositivity.HomologicalAlgebra.KoszulDirectedUnion
public import SerrePositivity.CommutativeAlgebra.FrobeniusKoszulLimit

/-! # Perfection の Koszul ホモロジーと近似環の極限

近似環の増大列は perfection を覆う。その Koszul ホモロジーを有向極限で同定し、
全段に共通の消去冪と有限段の長さ公式を適用する。
通常の高次 Frobenius ホモロジーの正規化長さが零へ収束するという前提から、
perfection の Koszul ホモロジーの正規化長さの消滅を導く。
この収束そのものは本ファイルでは仮定であり、Roberts の結果との接続は別に残る。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section2

open IsLocalRing CategoryTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

attribute [local instance] rootStageAlgebra towerPerfectionAlgebra stagePerfectionAlgebra
  stageTowerPerfection

variable (A D : Type u) [CommRing A] [CommRing D] [IsDomain D]
    (p : ℕ) [Fact p.Prime] [CharP D p] [Algebra A (PerfectClosure D p)]
    {h : ℕ} (t : Fin h → A)

/-- 初段から各近似段へ送った元は、元の環からその段への標準写像と一致する。 -/
theorem perfectionApproximation_stageBaseMap (n : ℕ) (d : D) :
    subalgebraStageBaseMap (Tower A t p) (PerfectClosure D p)
      (perfectionApproximation D p (Tower A t p))
      (perfectionApproximation_monotone D p (Tower A t p)) n
      (perfectionApproximationBaseMap A D p t 0 d) =
        perfectionApproximationBaseMap A D p t n d := by
  apply Subtype.ext
  rw [subalgebraStageBaseMap_coe, perfectionApproximationBaseMap_coe,
    perfectionApproximationBaseMap_coe]

/-- Perfection の近似環の Koszul 図式。全段を塔上の複体として扱う。 -/
noncomputable abbrev perfectionKoszulDiagram {r : ℕ} (z : Fin r → D) :=
  subalgebraKoszulDiagram (Tower A t p) (PerfectClosure D p)
    (perfectionApproximation D p (Tower A t p))
    (perfectionApproximation_monotone D p (Tower A t p))
    (perfectionApproximationBaseMap A D p t 0 ∘ z)

/-- 近似環の Koszul ホモロジーの有向極限は、perfection のホモロジーに塔上で同型。 -/
noncomputable def perfectionKoszulHomologyDirectLimitEquiv {r : ℕ}
    (z : Fin r → D) (i : ℤ) :
    Module.DirectLimit (fun n ↦ ((perfectionKoszulDiagram A D p t z).obj n).homology i)
      (homologyStageMap (perfectionKoszulDiagram A D p t z) i) ≃ₗ[Tower A t p]
      (ModuleCat.restrictScalars (algebraMap (Tower A t p) (PerfectClosure D p))).obj
        ((koszulComplex (PerfectClosure.of D p ∘ z)).homology i) := by
  have e := subalgebraKoszulHomologyDirectLimitEquiv (Tower A t p) (PerfectClosure D p)
    (perfectionApproximation D p (Tower A t p))
    (perfectionApproximation_monotone D p (Tower A t p))
    (perfectionApproximationBaseMap A D p t 0 ∘ z)
    (exists_mem_perfectionApproximation D p (Tower A t p)) i
  have he : (perfectionApproximation D p (Tower A t p) 0).val ∘
      (perfectionApproximationBaseMap A D p t 0 ∘ z) = PerfectClosure.of D p ∘ z := by
    funext j
    exact perfectionApproximationBaseMap_coe A D p t 0 (z j)
  rw [he] at e
  exact e

variable [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [Module.Finite A D]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]

/-- 高次 Frobenius Koszul ホモロジーの通常長さの消滅極限を、perfection 上の消滅へ移す。
近似段の有限長性・平坦性・共通の消去冪・有向被覆は元の仮定から供給する。 -/
theorem towerLengthFun_perfection_koszulHomology_eq_zero_of_tendsto
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℤ)
    (hlim : Filter.Tendsto (fun n : ℕ ↦
      (Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop (nhds 0)) :
    letI := Module.compHom ((koszulComplex (PerfectClosure.of D p ∘ z)).homology i)
      (algebraMap (Tower A t p) (PerfectClosure D p))
    towerLengthFun A t p ((koszulComplex (PerfectClosure.of D p ∘ z)).homology i) = 0 := by
  have htm : ∀ j, t j ∈ maximalIdeal A :=
    fun j ↦ ht ▸ Ideal.subset_span (Set.mem_range_self j)
  let R := Tower A t p
  let C := PerfectClosure D p
  let B := perfectionApproximation D p R
  let hB := perfectionApproximation_monotone D p R
  let z₀ := perfectionApproximationBaseMap A D p t 0 ∘ z
  have he (n : ℕ) : subalgebraStageBaseMap R C B hB n ∘ z₀ =
      perfectionApproximationBaseMap A D p t n ∘ z := by
    funext j
    exact perfectionApproximation_stageBaseMap A D p t n (z j)
  obtain ⟨N, hN⟩ := exists_uniform_pow_torsion_perfectionApproximation_koszul
    A D p t hinj hbase z hz
  have hstage (n : ℕ) : (towerLength A t p htm).len
      ((ModuleCat.restrictScalars (algebraMap R (B n))).obj
        ((koszulComplex (subalgebraStageBaseMap R C B hB n ∘ z₀)).homology i)) =
      (Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
    rw [he]
    exact (perfectionApproximation_koszulHomology_length
      A D p t ht hdim hinj hres hbase hsep n z hz i).1
  have hzlim := subalgebraKoszulHomology_len_eq_zero R C B hB z₀
    (exists_mem_perfectionApproximation D p R) (towerLength A t p htm)
    (towerLength_hasSup A t p htm) i N (fun n ↦ by
      rw [he]
      exact hN n i) (by
        have heq : (fun n ↦ (towerLength A t p htm).len
            ((ModuleCat.restrictScalars (algebraMap R (B n))).obj
              ((koszulComplex (subalgebraStageBaseMap R C B hB n ∘ z₀)).homology i))) =
            (fun n ↦ (Module.length D
              ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
                (stageRank h p n : ℝ≥0∞)) := funext hstage
        rw [heq]
        exact hlim)
  have he₀ : (B 0).val ∘ z₀ = PerfectClosure.of D p ∘ z := by
    funext j
    exact perfectionApproximationBaseMap_coe A D p t 0 (z j)
  rw [he₀] at hzlim
  exact hzlim

/-- 任意の両立する塔作用について、同じ消滅を定理2.5の `λ_D` と homological 添字で述べる。 -/
theorem towerLengthOn_perfection_koszulHomology_eq_zero_of_tendsto
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    [Algebra D (PerfectClosure D p)]
    [instTower : Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℕ)
    (hlim : Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (koszulHomologySelf (fun j ↦ z j ^ (p ^ n)) i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop (nhds 0)) :
    (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
      (koszulHomologySelf (algebraMap D (PerfectClosure D p) ∘ z) i) = 0 := by
  have heq : instTower = towerPerfectionAlgebra A D p t := by
    apply Algebra.algebra_ext
    intro x
    exact AlgHom.congr_fun (towerToPerfect_unique A (PerfectClosure D p) t p
      (IsScalarTower.toAlgHom A (Tower A t p) (PerfectClosure D p))) x
  subst instTower
  have hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A D (PerfectClosure D p), hcanonical]
  have he : algebraMap D (PerfectClosure D p) ∘ z = PerfectClosure.of D p ∘ z := by
    rw [hcanonical]
  rw [he]
  exact towerLengthFun_perfection_koszulHomology_eq_zero_of_tendsto
    A D p t ht hdim hinj hres hbase hsep z hz (-(i : ℤ)) hlim

end SerrePositivity.Section2
