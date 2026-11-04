module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion

/-! # perfectoid イデアルの冪と根基

## 概要

`p` の正の冪や単元倍で生成元を取り替えても perfectoid イデアルが変わらないこと、ねじれ商が perfectoid なら `p` 倍が零になることを示す。perfectoid イデアルが根基イデアルであること、`(g)` の根基がそれに含まれること、生成元の任意の正の冪で同じイデアルになることを与える。

## 方針

perfectoid 化の普遍性と、`p` が冪零なら `p = 0` であることを使う。被約性は perfectoid 環の一般の被約性（CommutativeAlgebra/Perfectoid/Torsion）から得る。

## 規約

差の almost 零性はここでは主張しない。旧 `CommutativeAlgebra/PerfectoidIdealPowers`・`PerfectoidIdealRadical`。

## 使われ方

`PerfectoidIdeal/Cover`、CLMST。
-/

@[expose] public noncomputable section

universe u

section PerfectoidIdealPowersPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- kがgのperfectoidイデアルに入れば、kのperfectoidイデアルもそこに含まれる。 -/
theorem perfectoidIdeal_le_of_mem {g k : R} (hk : k ∈ perfectoidIdeal R p hR g) :
    perfectoidIdeal R p hR k ≤ perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {k}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton k)
  let T := QuotientPerfectoidization R (Ideal.span {g}) p hR
  let κ : R →+* T := (toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  let f : R ⧸ Ideal.span {k} →+* T := Ideal.Quotient.lift _ κ
    ((Ideal.span_singleton_le_iff_mem _).mpr hk)
  let hg := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  let hk' := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {k}) p hR
  let l := IsPerfectoidization.lift hk' hg.1 f
  intro x hx
  change toQuotientPerfectoidization R (Ideal.span {k}) p hR
    (Ideal.Quotient.mk (Ideal.span {k}) x) = 0 at hx
  change κ x = 0
  have he := RingHom.congr_fun (IsPerfectoidization.lift_comp hk' hg.1 f)
    (Ideal.Quotient.mk (Ideal.span {k}) x)
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact he.symm

/-- pの正冪のperfectoidイデアルはp自身のperfectoidイデアルと一致する。 -/
theorem perfectoidIdeal_p_pow_eq (n : ℕ) (hn : 0 < n) :
    perfectoidIdeal R p hR ((p : R) ^ n) = perfectoidIdeal R p hR (p : R) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {(p : R) ^ n}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton ((p : R) ^ n))
  let T := QuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR
  let κ : R →+* T := (toQuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}))
  have hT : IsIntegralPerfectoid T p :=
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR).1
  have hz : (p : T) ^ n = 0 := by
    have hh := (span_le_perfectoidIdeal R p hR ((p : R) ^ n))
      (Ideal.subset_span (Set.mem_singleton _))
    change κ ((p : R) ^ n) = 0 at hh
    simpa only [map_pow, map_natCast] using hh
  have hp0 : (p : T) = 0 := hT.p_eq_zero_of_isNilpotent T p ⟨n, hz⟩
  apply le_antisymm
  · apply perfectoidIdeal_mono
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn
  · apply perfectoidIdeal_le_of_mem
    change κ (p : R) = 0
    simpa only [map_natCast] using hp0

/-- 単元倍はperfectoidイデアルを変えない。 -/
theorem perfectoidIdeal_mul_unit_eq (g a : R) (ha : IsUnit a) :
    perfectoidIdeal R p hR (g * a) = perfectoidIdeal R p hR g := by
  have hs : Ideal.span {g * a} = Ideal.span {g} := Ideal.span_singleton_mul_right_unit ha g
  exact le_antisymm (perfectoidIdeal_mono R p hR hs.le)
    (perfectoidIdeal_mono R p hR hs.ge)

/-- perfectoidなpねじれ商があれば、p^c g'で消える射からg'のperfectoidイデアルの像はpねじれ。
商のperfectoid性を単にpの非零因子性から推論しない。 -/
theorem perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hQ : IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p)
    (f : R →+* S) (g' : R) (c : ℕ) (hg : (p : S) ^ c * f g' = 0)
    (x : R) (hx : x ∈ perfectoidIdeal R p hR g') : (p : S) * f x = 0 := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g'}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g')
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  have hfg : g' ∈ RingHom.ker (q.comp f) := by
    change q (f g') = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hS.p_mul_eq_zero_of_pow_mul_eq_zero S p c (f g') hg)
  let k : R ⧸ Ideal.span {g'} →+* S ⧸ pTorsionIdeal S p :=
    Ideal.Quotient.lift _ (q.comp f) ((Ideal.span_singleton_le_iff_mem _).mpr hfg)
  let hu := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g'}) p hR
  have he := RingHom.congr_fun (IsPerfectoidization.lift_comp hu hQ k)
    (Ideal.Quotient.mk (Ideal.span {g'}) x)
  change toQuotientPerfectoidization R (Ideal.span {g'}) p hR
    (Ideal.Quotient.mk (Ideal.span {g'}) x) = 0 at hx
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm

end SerrePositivity

end PerfectoidIdealPowersPart

section PerfectoidIdealRadicalPart

namespace SerrePositivity
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- The actual kernel defining the perfectoid ideal is radical for every g. -/
theorem perfectoidIdeal_isRadical (g : R) :
    (perfectoidIdeal R p hR g).IsRadical := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let T := QuotientPerfectoidization R (Ideal.span {g}) p hR
  let κ : R →+* T := (toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  have hT : IsIntegralPerfectoid T p :=
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).1
  let := hT.isReduced T p
  intro x hx
  obtain ⟨n, hn⟩ := hx
  change κ x = 0
  apply IsReduced.eq_zero
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact hn

/-- Every root of the original principal ideal lies in its perfectoid ideal. -/
theorem radical_span_le_perfectoidIdeal (g : R) :
    (Ideal.span {g}).radical ≤ perfectoidIdeal R p hR g :=
  (perfectoidIdeal_isRadical R p hR g).radical_le_iff.mpr
    (span_le_perfectoidIdeal R p hR g)

/-- Positive powers of any element define the same perfectoid ideal.
No regularity of g or of p is required. -/
theorem perfectoidIdeal_pow_eq (g : R) (n : ℕ) (hn : 0 < n) :
    perfectoidIdeal R p hR (g ^ n) = perfectoidIdeal R p hR g := by
  apply le_antisymm
  · apply perfectoidIdeal_mono
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn
  · apply perfectoidIdeal_le_of_mem
    apply perfectoidIdeal_isRadical R p hR (g ^ n)
    exact ⟨n, (span_le_perfectoidIdeal R p hR (g ^ n))
      (Ideal.subset_span (Set.mem_singleton _))⟩

end SerrePositivity

end PerfectoidIdealRadicalPart
