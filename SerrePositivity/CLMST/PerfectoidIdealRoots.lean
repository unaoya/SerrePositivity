module

public import SerrePositivity.CommutativeAlgebra.Perfectoidization
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import SerrePositivity.CommutativeAlgebra.PerfectoidCharacteristicP
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # 被約な目標への核と根の所属

商環から被約環への写像は、生成イデアルに冪が属する元を消す。
perfectoid ideal の核の定義へこの一般論を適用し、完備塔の根の座標についても具体化する。
一般の主イデアル商では被約性を明示的な引数として保つ。
pによる商は標数pのperfectoid環がperfectであることから被約性を供給する。
被約性の引用や大域的なインスタンスは追加しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open Section2

/-- 被約環への写像の核は、生成イデアルに冪が属するすべての元を含む。 -/
theorem mem_kernel_comp_quotient_of_pow_mem_span
    {R C : Type u} [CommRing R] [CommRing C] [IsReduced C]
    (g : R) (f : R ⧸ Ideal.span {g} →+* C) (x : R) (k : ℕ)
    (hx : x ^ k ∈ Ideal.span {g}) :
    x ∈ RingHom.ker (f.comp (Ideal.Quotient.mk (Ideal.span {g}))) := by
  change f (Ideal.Quotient.mk (Ideal.span {g}) x) = 0
  apply IsReduced.eq_zero
  refine ⟨k, ?_⟩
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- perfectoid ideal の核の定義で使われる、主イデアル商の選ばれた perfectoid 化。 -/
abbrev perfectoidQuotient (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) : Type u :=
  letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  Perfectoidization R (R ⧸ Ideal.span {g}) p hR

/-- 選ばれた perfectoid 化の被約性が与えられれば、冪の所属から perfectoid ideal への所属が従う。
被約性は現在未供給の条件であり、型クラスの大域的登録では隠さない。 -/
theorem mem_perfectoidIdeal_of_pow_mem_span_of_reduced
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hred : IsReduced (perfectoidQuotient R p hR g))
    (x : R) (k : ℕ) (hx : x ^ k ∈ Ideal.span {g}) :
    x ∈ perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let : IsReduced (Perfectoidization R (R ⧸ Ideal.span {g}) p hR) := hred
  exact mem_kernel_comp_quotient_of_pow_mem_span g
    (toPerfectoidization R (R ⧸ Ideal.span {g}) p hR) x k hx

/-- pによる商のperfectoid化は標数pなので、定義から証明した被約性を使える。 -/
theorem perfectoidQuotient_p_isReduced
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) : IsReduced (perfectoidQuotient R p hR (p : R)) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {(p : R)}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton (p : R))
  let Q := R ⧸ Ideal.span {(p : R)}
  let T := Perfectoidization R Q p hR
  let f := toPerfectoidization R Q p hR
  have hT : IsIntegralPerfectoid T p := (isPerfectoidization_toPerfectoidization R Q p hR).1
  have hpQ : (p : Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)}))]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hpT : (p : T) = 0 := by
    calc
      (p : T) = f (p : Q) := (map_natCast f p).symm
      _ = f 0 := congrArg f hpQ
      _ = 0 := f.map_zero
  exact hT.isReduced_of_p_eq_zero T p hpT

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 有限段の根の座標を完備塔へ移した元。 -/
def completedTowerRoot (n : ℕ) (i : Fin h) : CompletedTower A t p :=
  algebraMap (TowerStage A t p n) (CompletedTower A t p) (stageX A t p n i)

omit [Fact p.Prime] in
/-- 完備塔の根の座標の `p^n` 乗は、基底環の対応する座標の標準像である。 -/
@[simp] theorem completedTowerRoot_pow (n : ℕ) (i : Fin h) :
    completedTowerRoot A t p n i ^ (p ^ n) =
      algebraMap A (CompletedTower A t p) (t i) := by
  rw [completedTowerRoot, ← map_pow]
  change algebraMap (TowerStage A t p n) (CompletedTower A t p)
    (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i) ^ (p ^ n)) = _
  rw [mk_X_pow, ← IsScalarTower.algebraMap_apply A (TowerStage A t p n) (CompletedTower A t p)]

/-- 基底の座標が p であるとき、完備塔のその根は `(p)_perfd` に属する。
選ばれた `(C/p)_perfd` の被約性を明示的に受け取り、他の入力は用いない。 -/
theorem completedTowerRoot_mem_perfectoidIdeal_p_of_reduced
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (hred : IsReduced (perfectoidQuotient (CompletedTower A t p) p hperf
      (p : CompletedTower A t p)))
    (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    completedTowerRoot A t p n i ∈
      perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) := by
  apply mem_perfectoidIdeal_of_pow_mem_span_of_reduced _ p hperf _ hred _ (p ^ n)
  rw [completedTowerRoot_pow, hti, map_natCast]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- pを座標に含む塔の全てのp冪根は、被約性を追加せず(p)_perfdへ入る。 -/
theorem completedTowerRoot_mem_perfectoidIdeal_p
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    completedTowerRoot A t p n i ∈
      perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) :=
  completedTowerRoot_mem_perfectoidIdeal_p_of_reduced A t p hperf
    (perfectoidQuotient_p_isReduced (CompletedTower A t p) p hperf) n i hti

end SerrePositivity.CLMST
