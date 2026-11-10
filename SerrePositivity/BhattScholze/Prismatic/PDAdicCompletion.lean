module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra

/-!
# p 進完備化への分冪の延長

## 概要
p を含む分冪イデアルの構造を、環の p 進完備化に延長する
（Berthelot–Ogus, Notes on Crystalline Cohomology, 3.20）。

## 方針
分冪が降りる冪商の両立する分冪を使う。

## 規約
一般の基底では `p^{e+2}` から塔を取る。
`γ_n(p^{e+2}a) = (p^{e+1}a)^n γ_n(p)` であり、`n ≥ 2` なら
`(e+1)n ≥ e+2` なので、分冪がこの冪で割った商に降りる。
この余終部分での合同から完備化上の分冪を定める。

## 使われ方
基底の分冪と両立する p 完備分冪包、結晶サイトの冪零の塔。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion

open AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable (p : ℕ) (δ : DividedPowers I) (hp : (p : R) ∈ I)

local notation "P" => Ideal.span {(p : R)}
local notation "C" => AdicCompletion P R

include hp in
private theorem primePower_le (e : ℕ) : P ^ (e + 2) ≤ I :=
  (Ideal.pow_le_pow_right (show 1 ≤ e + 2 by omega)).trans
    (by simpa only [pow_one] using (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp)))

include hp in
/-- `p^{e+2}` は分冪部分イデアル。指数を 2 から取ることで
`γ_n(p)` の追加の p 可除性を仮定せずに、冪商への分冪の降下を保証する。 -/
theorem primePower_isSubDPIdeal (e : ℕ) : δ.IsSubDPIdeal (P ^ (e + 2)) := by
  refine ⟨primePower_le p hp e, ?_⟩
  intro n hn x hx
  rcases n with _ | n
  · exact (hn rfl).elim
  rcases n with _ | n
  · simpa only [δ.dpow_one (primePower_le p hp e hx)] using hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  have hfactor : (p : R) ^ (e + 2) * a = ((p : R) ^ (e + 1) * a) * p := by
    rw [pow_succ (p : R) (e + 1)]
    ac_rfl
  rw [hfactor, δ.dpow_mul hp, mul_pow]
  apply Ideal.mul_mem_right
  apply Ideal.mul_mem_right
  rw [← pow_mul]
  apply Ideal.pow_le_pow_right (I := P) (show e + 2 ≤ (e + 1) * (n + 2) by nlinarith)
  exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : R)) _

/-- `p^{e+2}` による商の分冪。 -/
def quotientDividedPowers (e : ℕ) :
    DividedPowers (I.map (Ideal.Quotient.mk (P ^ (e + 2)))) :=
  DividedPowers.Quotient.dividedPowers δ
    (by rw [inf_of_le_left (primePower_le p hp e)]; exact primePower_isSubDPIdeal p δ hp e)

@[simp]
theorem quotientDividedPowers_mk (e n : ℕ) {x : R} (hx : x ∈ I) :
    (quotientDividedPowers p δ hp e).dpow n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (δ.dpow n x) :=
  DividedPowers.Quotient.dpow_apply δ _ hx

private theorem eval_transition {a b : ℕ} (h : a ≤ b) (x : C) :
    Ideal.Quotient.factorPow P h (evalₐ P b x) = evalₐ P a x := by
  rw [← factor_eval_eq_evalₐ P _ (Ideal.mul_le_left (I := P ^ a) (J := ⊤)),
    ← factor_eval_eq_evalₐ P _ (Ideal.mul_le_left (I := P ^ b) (J := ⊤))]
  have ht := transitionMap_comp_eval_apply P R h x
  change transitionMap P R h (eval P R b x) = eval P R a x at ht
  rw [← ht]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (eval P R b x)
  rw [← hr]
  rfl

private theorem ext_shift {x y : C} (h : ∀ e, evalₐ P (e + 2) x = evalₐ P (e + 2) y) :
    x = y := by
  apply ext_evalₐ
  intro e
  have he : e ≤ e + 2 := by omega
  rw [← eval_transition p he x, ← eval_transition p he y, h e]

/-- 完備化の分冪イデアル。p を含む開イデアルなのでその拡大は閉じている。 -/
def ideal (I : Ideal R) : Ideal C := I.map (algebraMap R C)

include hp in
private theorem eval_mem_iff (e : ℕ) (x : C) :
    evalₐ P (e + 2) x ∈ I.map (Ideal.Quotient.mk (P ^ (e + 2))) ↔ x ∈ ideal p I := by
  unfold ideal
  rw [← adicCompletionOpenQuotientMap_ker P I (e + 2) (primePower_le p hp e)
    (Submodule.fg_span_singleton (p : R))]
  change _ ↔ Ideal.Quotient.factor (primePower_le p hp e) (evalₐ P (e + 2) x) = 0
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ P (e + 2) x)
  rw [← hr]
  exact ⟨fun hrI => by
    obtain ⟨s, hs, heq⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hrI
    rw [← heq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hs,
    fun hrI => Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp hrI)⟩

include hp in
private theorem exists_rep {x : C} (hx : x ∈ ideal p I) (e : ℕ) :
    ∃ a ∈ I, Ideal.Quotient.mk (P ^ (e + 2)) a = evalₐ P (e + 2) x :=
  (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
    ((eval_mem_iff p hp e x).mpr hx)

private def rep {x : C} (hx : x ∈ ideal p I) (e : ℕ) : R :=
  (exists_rep p hp hx e).choose

private theorem rep_mem {x : C} (hx : x ∈ ideal p I) (e : ℕ) :
    rep p hp hx e ∈ I := (exists_rep p hp hx e).choose_spec.1

private theorem rep_eval {x : C} (hx : x ∈ ideal p I) (e : ℕ) :
    Ideal.Quotient.mk (P ^ (e + 2)) (rep p hp hx e) = evalₐ P (e + 2) x :=
  (exists_rep p hp hx e).choose_spec.2

include hp in
private theorem dpow_congr (e n : ℕ) {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (h : Ideal.Quotient.mk (P ^ (e + 2)) a = Ideal.Quotient.mk (P ^ (e + 2)) b) :
    Ideal.Quotient.mk (P ^ (e + 2)) (δ.dpow n a) =
      Ideal.Quotient.mk (P ^ (e + 2)) (δ.dpow n b) := by
  rw [← quotientDividedPowers_mk p δ hp e n ha, ← quotientDividedPowers_mk p δ hp e n hb, h]

private def sequence (n : ℕ) {x : C} (hx : x ∈ ideal p I) : AdicCauchySequence P R :=
  ⟨fun e => δ.dpow n (rep p hp hx e), by
    intro a b hab
    apply SModEq.sub_mem.mpr
    rw [smul_eq_mul, Ideal.mul_top]
    apply Ideal.pow_le_pow_right (show a ≤ a + 2 by omega)
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    apply dpow_congr p δ hp a n (rep_mem p hp hx a) (rep_mem p hp hx b)
    have h : a + 2 ≤ b + 2 := Nat.add_le_add_right hab 2
    rw [rep_eval p hp hx a, ← eval_transition p h x, ← rep_eval p hp hx b]
    rfl⟩

private def dpow (n : ℕ) (x : C) : C := by
  classical
  exact if hx : x ∈ ideal p I then AdicCompletion.mk P R (sequence p δ hp n hx) else 0

private theorem eval_dpow (e n : ℕ) {x : C} (hx : x ∈ ideal p I) :
    evalₐ P (e + 2) (dpow p δ hp n x) =
      (quotientDividedPowers p δ hp e).dpow n (evalₐ P (e + 2) x) := by
  classical
  rw [dpow, dite_eq_left hx, evalₐ_mk]
  change Ideal.Quotient.mk (P ^ (e + 2)) (δ.dpow n (rep p hp hx (e + 2))) = _
  rw [← eval_transition p (show e + 2 ≤ (e + 2) + 2 by omega) x,
    ← rep_eval p hp hx (e + 2)]
  exact (quotientDividedPowers_mk p δ hp e n (rep_mem p hp hx (e + 2))).symm

private theorem dpow_mem {n : ℕ} {x : C} (hn : n ≠ 0) (hx : x ∈ ideal p I) :
    dpow p δ hp n x ∈ ideal p I :=
  (eval_mem_iff p hp 0 _).mp (by
    rw [eval_dpow p δ hp 0 n hx]
    exact (quotientDividedPowers p δ hp 0).dpow_mem hn ((eval_mem_iff p hp 0 x).mpr hx))

/-- p 完備化に延長した分冪。余終な各有限商への射影が分冪を保つ。 -/
def dividedPowers : DividedPowers (ideal p I) where
  dpow := dpow p δ hp
  dpow_null hx := by classical exact dite_eq_right hx
  dpow_zero hx := ext_shift p fun e => by
    rw [eval_dpow p δ hp e 0 hx, (quotientDividedPowers p δ hp e).dpow_zero
      ((eval_mem_iff p hp e _).mpr hx), map_one]
  dpow_one hx := ext_shift p fun e => by
    rw [eval_dpow p δ hp e 1 hx, (quotientDividedPowers p δ hp e).dpow_one
      ((eval_mem_iff p hp e _).mpr hx)]
  dpow_mem := dpow_mem p δ hp
  dpow_add {n x y} hx hy := ext_shift p fun e => by
    rw [eval_dpow p δ hp e n ((ideal p I).add_mem hx hy), map_add, map_sum,
      (quotientDividedPowers p δ hp e).dpow_add ((eval_mem_iff p hp e _).mpr hx)
        ((eval_mem_iff p hp e _).mpr hy)]
    simp only [map_mul, eval_dpow p δ hp e _ hx, eval_dpow p δ hp e _ hy]
  dpow_mul {n a x} hx := ext_shift p fun e => by
    rw [eval_dpow p δ hp e n ((ideal p I).mul_mem_left a hx), map_mul, map_mul, map_pow,
      eval_dpow p δ hp e n hx, (quotientDividedPowers p δ hp e).dpow_mul
        ((eval_mem_iff p hp e _).mpr hx)]
  mul_dpow {m n x} hx := ext_shift p fun e => by
    simp only [map_mul, map_natCast, eval_dpow p δ hp e _ hx]
    exact (quotientDividedPowers p δ hp e).mul_dpow ((eval_mem_iff p hp e _).mpr hx)
  dpow_comp {m n x} hn hx := ext_shift p fun e => by
    rw [eval_dpow p δ hp e m (dpow_mem p δ hp hn hx), eval_dpow p δ hp e n hx,
      map_mul, map_natCast, eval_dpow p δ hp e (m * n) hx,
      (quotientDividedPowers p δ hp e).dpow_comp hn ((eval_mem_iff p hp e _).mpr hx)]

/-- 完備化の単位は分冪を保つ。 -/
theorem unit_isDPMorphism : δ.IsDPMorphism (dividedPowers p δ hp) (algebraMap R C) := by
  refine ⟨le_rfl, fun {n} x hx => ext_shift p fun e => ?_⟩
  change evalₐ P (e + 2) (dpow p δ hp n (of P R x)) =
    evalₐ P (e + 2) (of P R (δ.dpow n x))
  have hm : of P R x ∈ ideal p I := Ideal.mem_map_of_mem (algebraMap R C) hx
  rw [eval_dpow p δ hp e n hm,
    evalₐ_of, evalₐ_of, quotientDividedPowers_mk p δ hp e n hx]

/-- p 進完備化は、完備化した環の p に関して完備。 -/
theorem isAdicComplete :
    IsAdicComplete (Ideal.span {(p : C)}) C := by
  have hmap : (P).map (algebraMap R C) = Ideal.span {(p : C)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : R))

private theorem map_eval_eq {E : Type*} [CommRing E] (f : C →+* E) (e : ℕ) {x y : C}
    (h : evalₐ P e x = evalₐ P e y) :
    Ideal.Quotient.mk ((Ideal.span {(p : E)}) ^ e) (f x) =
      Ideal.Quotient.mk ((Ideal.span {(p : E)}) ^ e) (f y) := by
  have hxy : x - y ∈ RingHom.ker (evalₐ P e).toRingHom := by
    change evalₐ P e (x - y) = 0
    rw [map_sub, h, sub_self]
  rw [adicCompletion_ker_eval_eq_pow_map P (Submodule.fg_span_singleton (p : R)),
    Ideal.map_span, Set.image_singleton, map_natCast] at hxy
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [← map_sub]
  have hm := Ideal.mem_map_of_mem f hxy
  rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast] at hm

/-- 分離な標的への環射は、完備化前の制限が分冪を保てば分冪を保つ。 -/
theorem isDPMorphism_of_comp {E : Type*} [CommRing E] {L : Ideal E} (ε : DividedPowers L)
    [IsHausdorff (Ideal.span {(p : E)}) E] (f : C →+* E)
    (hf : δ.IsDPMorphism ε (f.comp (algebraMap R C))) :
    (dividedPowers p δ hp).IsDPMorphism ε f := by
  have hmap : (ideal p I).map f ≤ L := by
    unfold ideal
    rw [Ideal.map_map]
    exact hf.ideal_comp
  have hpE : (p : E) ∈ L := by
    simpa only [map_natCast] using hf.ideal_comp (Ideal.mem_map_of_mem _ hp)
  refine ⟨hmap, fun {n} x hx => ?_⟩
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : E)})).mpr
  intro j
  apply SModEq.sub_mem.mpr
  rw [smul_eq_mul, Ideal.mul_top]
  apply Ideal.pow_le_pow_right (show j ≤ j + 2 by omega)
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  let q := Ideal.Quotient.mk ((Ideal.span {(p : E)}) ^ (j + 2))
  obtain ⟨a, ha, hax⟩ := exists_rep p hp hx j
  have hax' : evalₐ P (j + 2) x = evalₐ P (j + 2) (of P R a) := by
    rw [evalₐ_of, hax]
  have hfa : f (of P R a) ∈ L := hf.ideal_comp (Ideal.mem_map_of_mem _ ha)
  have hfx : f x ∈ L := hmap (Ideal.mem_map_of_mem f hx)
  have hdp : evalₐ P (j + 2) ((dividedPowers p δ hp).dpow n x) =
      evalₐ P (j + 2) (of P R (δ.dpow n a)) := by
    change evalₐ P (j + 2) (dpow p δ hp n x) = _
    rw [eval_dpow p δ hp j n hx, ← hax, quotientDividedPowers_mk p δ hp j n ha, evalₐ_of]
  change q (ε.dpow n (f x)) = q (f ((dividedPowers p δ hp).dpow n x))
  rw [map_eval_eq p f (j + 2) hdp,
    ← show ε.dpow n (f (of P R a)) = f (of P R (δ.dpow n a)) from hf.dpow_comp a ha,
    ← quotientDividedPowers_mk p ε hpE j n hfx,
    ← quotientDividedPowers_mk p ε hpE j n hfa,
    map_eval_eq p f (j + 2) hax']

end SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion
