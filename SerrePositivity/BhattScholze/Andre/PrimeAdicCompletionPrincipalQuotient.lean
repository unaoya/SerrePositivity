module

public import SerrePositivity.BhattScholze.Andre.PrimeAdicCompletionUniversal
public import SerrePositivity.CommutativeAlgebra.AdicStrictQuotient
public import SerrePositivity.CommutativeAlgebra.AdicCompletionQuotient
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# André A1-a：全冪商で正則な入力による完備化の商

## 概要

各 p 冪商で正則な入力を使うと、p 完備化をその入力で割った環も p 完備となる。
BS Rem 7.15（著者版 p.62）のモニック商と完備化の交換への準備。

## 方針

全冪商の正則性から乗法のフィルトレーション比較を直接得る。
完備化の冪商比較で同じ正則性を完備環へ移す。原典を補う一様な比較による経路。

## 規約

p 正則性・Noether 性・素数性を前提としない。全冪商の入力の正則性を明示する。

## 使われ方

モニック入力の全係数冪商での正則性を供給し、原典の完備入力環を接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R]

/-- 概要：全ての a 冪商で正則な元による商は a 完備。
方針：各冪商の正則性で乗法写像の逆像のフィルトレーションを比較する。
規約：a 自体の正則性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）のモニック商の完備性。 -/
theorem isAdicComplete_principal_quotient_of_regular_powers (a g : R)
    [IsAdicComplete (Ideal.span {a}) R]
    (hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {a ^ n})
      (Ideal.Quotient.mk (Ideal.span {a ^ n}) g)) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a})
      (R ⧸ Ideal.span {g}) := by
  let m := LinearMap.mulLeft R g
  have hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap m ((Ideal.span {a}) ^ (n + k) • (⊤ : Submodule R R)) ≤
        (Ideal.span {a}) ^ n • (⊤ : Submodule R R) := by
    refine ⟨0, fun n x hx => ?_⟩
    simp only [Submodule.mem_comap, m, LinearMap.mulLeft_apply, Nat.add_zero,
      Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      at hx ⊢
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hg n
    change Ideal.Quotient.mk (Ideal.span {a ^ n}) g *
      Ideal.Quotient.mk (Ideal.span {a ^ n}) x =
        Ideal.Quotient.mk (Ideal.span {a ^ n}) g * 0
    rw [← map_mul, mul_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hx)
  have hrange : m.range = (Ideal.span {g} : Submodule R R) := by
    ext x
    simp only [LinearMap.mem_range, m, LinearMap.mulLeft_apply,
      Ideal.mem_span_singleton, dvd_def]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  let : IsAdicComplete (Ideal.span {a}) (R ⧸ Ideal.span {g}) := by
    rw [← hrange]
    exact isAdicComplete_quotient_range_of_uniform_filtration_bound (Ideal.span {a}) m hbound
  have he : (Ideal.span {a}).map (algebraMap R (R ⧸ Ideal.span {g})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← he]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

variable (p : ℕ)
local notation "Jp" => Ideal.span {(p : R)}
local notation "C" => AdicCompletion Jp R
local notation "j" => algebraMap R C

/-- 概要：p 完備化はその環上の p 主イデアルに関して完備。
方針：有限生成性による完備性をイデアルの拡張で移す。
規約：係数環上の加群完備性と環自身の完備性を明示的に比較する。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力環。 -/
theorem primeAdicCompletion_isAdicComplete : IsAdicComplete (Ideal.span {(p : C)}) C := by
  have h := (IsAdicComplete.map_algebraMap_iff (I := Jp) (S := C) (M := C)).mpr
    (AdicCompletion.isAdicComplete (M := R) (Submodule.fg_span_singleton (p : R)))
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h

/-- 概要：入力の p 冪商での正則性は p 完備化の同じ冪商で保存される。
方針：完備化の冪商同型と代表元公式で正則性を移す。
規約：p 自体の正則性は使わない。
使われ方：BS Rem 7.15（著者版 p.62）の完備化後のモニック入力。 -/
theorem primeAdicCompletion_regular_mod_power (g : R) (n : ℕ)
    (hg : IsSMulRegular (R ⧸ Ideal.span {(p : R) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) g)) :
    IsSMulRegular (C ⧸ Ideal.span {(p : C) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : C) ^ n}) (j g)) := by
  have hr : IsSMulRegular (R ⧸ Jp ^ n) (Ideal.Quotient.mk (Jp ^ n) g) := by
    rw [Ideal.span_singleton_pow]
    exact hg
  have h : IsSMulRegular (C ⧸ ((Jp).map j) ^ n)
      (Ideal.Quotient.mk (((Jp).map j) ^ n) (j g)) := by
    let e := adicCompletionPowQuotientEquiv Jp (Submodule.fg_span_singleton (p : R)) n
    intro x y hxy
    apply e.injective
    apply hr
    have he := congrArg e hxy
    have hc : e (Ideal.Quotient.mk (((Jp).map j) ^ n) (j g)) =
        Ideal.Quotient.mk (Jp ^ n) g :=
      adicCompletionPowQuotientEquiv_algebraMap Jp (Submodule.fg_span_singleton (p : R)) n g
    simpa only [smul_eq_mul, map_mul, hc] using he
  rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_pow] at h
  exact h

/-- 概要：全 p 冪商で正則な入力を p 完備化で割ると p 完備環を得る。
方針：冪商の正則性を完備化へ移し、一様なフィルトレーション比較を適用する。
規約：源の p 正則性や有界 p ねじれを追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の完備化と入力商の交換。 -/
theorem primeAdicCompletion_principal_quotient_isAdicComplete (g : R)
    (hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {(p : R) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) g)) :
    IsAdicComplete (Ideal.span {(p : C ⧸ Ideal.span {j g})})
      (C ⧸ Ideal.span {j g}) := by
  let := primeAdicCompletion_isAdicComplete R p
  have h := isAdicComplete_principal_quotient_of_regular_powers C (p : C) (j g)
    (fun n => primeAdicCompletion_regular_mod_power R p g n (hg n))
  simpa only [map_natCast] using h

end SerrePositivity.BhattScholze.Andre
