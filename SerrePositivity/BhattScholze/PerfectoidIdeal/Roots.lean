module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Powers
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRoots
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import SerrePositivity.CommutativeAlgebra.Perfection
public import Mathlib.RingTheory.Nilpotent.Basic
public import SerrePositivity.CommutativeAlgebra.ReducedSpectrum

/-! # perfectoid イデアルの商と根の所属

## 概要

主イデアル商の選んだ perfectoid 化を `perfectoidQuotient` と書き、perfectoid イデアルによる商との同型（`perfectoidIdealQuotientEquiv`）を与える。この商が被約であること（`p` を法としても）から、冪が `(g)` に入る元は perfectoid イデアルに入ることを示し、完備塔の根の座標（`Section2.completedTowerRoot`）が perfectoid イデアルに入ることを具体化する。
BS 著者版 Theorem 7.4 の全射性と §10.1 の核イデアルを、互換根の所属の判定に使う。

## 方針

被約な環への写像は、冪が生成イデアルに入る元を消す（`mem_kernel_comp_quotient_of_pow_mem_span`、CommutativeAlgebra/ReducedSpectrum）。被約性は一般の perfectoid の被約性から得る。

## 規約

被約性の引用や大域的な instance は加えない。旧 `CLMST/PerfectoidIdealRoots` の BS に依存する部分（2a で BS の下へ移した）。CLMST にあった `Section2.completedTowerRoot` の別名 5 つは削除した。

## 使われ方

CLMST の Prop 4.0.10（Cyclic*）と根のフィルトレーションの評価、`PerfectoidIdeal/Tor` の前段。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.Section2

/-- perfectoid ideal の核の定義で使われる、主イデアル商の選ばれた perfectoid 化。 -/
abbrev perfectoidQuotient (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) : Type u :=
  letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R (Ideal.span {g}) p hR

/-- 標準写像が全射なら、核で割った環は選ばれたperfectoid化そのものになる。
存在と普遍性だけで全射性が従うとは主張しない。 -/
def perfectoidIdealQuotientEquiv
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hsurj : letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
      Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR)) :
    R ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g ≃+* perfectoidQuotient R p hR g :=
  letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  RingHom.quotientKerEquivOfSurjective
    (hsurj.comp Ideal.Quotient.mk_surjective)

/-- 上の同型は元環からの二つの標準写像と両立する。 -/
@[simp] theorem perfectoidIdealQuotientEquiv_mk
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hsurj : letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
      Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR)) (x : R) :
    perfectoidIdealQuotientEquiv R p hR g hsurj
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) x) =
      (letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
        Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
       _root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR
         (Ideal.Quotient.mk (Ideal.span {g}) x)) := rfl

/-- 選ばれた perfectoid 化の被約性が与えられれば、冪の所属から perfectoid ideal への所属が従う。
被約性を明示的に受け取る互換入口。条件不要の入口は下の一般定理を使う。 -/
theorem mem_perfectoidIdeal_of_pow_mem_span_of_reduced
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hred : IsReduced (perfectoidQuotient R p hR g))
    (x : R) (k : ℕ) (hx : x ^ k ∈ Ideal.span {g}) :
    x ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let : IsReduced (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R (Ideal.span {g}) p hR) := hred
  exact mem_kernel_comp_quotient_of_pow_mem_span g
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR) x k hx

/-- Every chosen principal quotient perfectoidization is reduced, including p-torsion bases. -/
theorem perfectoidQuotient_isReduced
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) :
    IsReduced (perfectoidQuotient R p hR g) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).1.isReduced _ p

/-- Powers in the original principal ideal give membership without a reducedness hypothesis. -/
theorem mem_perfectoidIdeal_of_pow_mem_span
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g x : R) (k : ℕ)
    (hx : x ^ k ∈ Ideal.span {g}) : x ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g :=
  _root_.SerrePositivity.BhattScholze.Almost.radical_span_le_perfectoidIdeal R p hR g ⟨k, hx⟩

/-- Compatibility for the principal quotient by p. -/
theorem perfectoidQuotient_p_isReduced
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) : IsReduced (perfectoidQuotient R p hR (p : R)) :=
  perfectoidQuotient_isReduced R p hR (p : R)

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

theorem completedTowerRoot_mem_perfectoidIdeal
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (n : ℕ) (i : Fin h) :
    Section2.completedTowerRoot A t p n i ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) (t i)) := by
  apply mem_perfectoidIdeal_of_pow_mem_span _ p hperf _ _ (p ^ n)
  rw [Section2.completedTowerRoot_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- 基底の座標が p であるとき、完備塔のその根は `(p)_perfd` に属する。
選ばれた `(C/p)_perfd` の被約性を明示的に受け取り、他の入力は用いない。 -/
theorem completedTowerRoot_mem_perfectoidIdeal_p_of_reduced
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (hred : IsReduced (perfectoidQuotient (CompletedTower A t p) p hperf
      (p : CompletedTower A t p)))
    (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    Section2.completedTowerRoot A t p n i ∈
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) := by
  apply mem_perfectoidIdeal_of_pow_mem_span_of_reduced _ p hperf _ hred _ (p ^ n)
  rw [Section2.completedTowerRoot_pow, hti, map_natCast]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- pを座標に含む塔の全てのp冪根は、被約性を追加せず(p)_perfdへ入る。 -/
theorem completedTowerRoot_mem_perfectoidIdeal_p
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    Section2.completedTowerRoot A t p n i ∈
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) :=
  completedTowerRoot_mem_perfectoidIdeal_p_of_reduced A t p hperf
    (perfectoidQuotient_p_isReduced (CompletedTower A t p) p hperf) n i hti

end SerrePositivity.BhattScholze
