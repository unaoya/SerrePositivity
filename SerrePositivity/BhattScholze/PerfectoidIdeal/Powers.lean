module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion

/-! # perfectoid イデアルの冪と根基

## 概要

`p` の正の冪や単元倍で生成元を取り替えても perfectoid イデアルが変わらないこと、ねじれ商が perfectoid なら `p` 倍が零になることを示す。perfectoid イデアルが根基イデアルであること、`(g)` の根基がそれに含まれること、生成元の任意の正の冪で同じイデアルになることを与える。
BS 著者版 §10.1 の単項 perfectoid 核を、冪と根基に沿って比較する。

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
theorem BhattScholze.Almost.perfectoidIdeal_le_of_mem {g k : R} (hk : k ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR k ≤ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {k}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton k)
  let T := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R (Ideal.span {g}) p hR
  let κ : R →+* T := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  let f : R ⧸ Ideal.span {k} →+* T := Ideal.Quotient.lift _ κ
    ((Ideal.span_singleton_le_iff_mem _).mpr hk)
  let hg := _root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  let hk' := _root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {k}) p hR
  let l := _root_.SerrePositivity.IsPerfectoidization.lift hk' hg.1 f
  intro x hx
  change _root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {k}) p hR
    (Ideal.Quotient.mk (Ideal.span {k}) x) = 0 at hx
  change κ x = 0
  have he := RingHom.congr_fun (_root_.SerrePositivity.IsPerfectoidization.lift_comp hk' hg.1 f)
    (Ideal.Quotient.mk (Ideal.span {k}) x)
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact he.symm

/-- pの正冪のperfectoidイデアルはp自身のperfectoidイデアルと一致する。 -/
theorem BhattScholze.Almost.perfectoidIdeal_p_pow_eq (n : ℕ) (hn : 0 < n) :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR ((p : R) ^ n) = _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (p : R) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {(p : R) ^ n}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton ((p : R) ^ n))
  let T := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR
  let κ : R →+* T := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}))
  have hT : _root_.SerrePositivity.IsIntegralPerfectoid T p :=
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR).1
  have hz : (p : T) ^ n = 0 := by
    have hh := (_root_.SerrePositivity.BhattScholze.Almost.span_le_perfectoidIdeal R p hR ((p : R) ^ n))
      (Ideal.subset_span (Set.mem_singleton _))
    change κ ((p : R) ^ n) = 0 at hh
    simpa only [map_pow, map_natCast] using hh
  have hp0 : (p : T) = 0 := hT.p_eq_zero_of_isNilpotent T p ⟨n, hz⟩
  apply le_antisymm
  · apply _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mono
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn
  · apply _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_le_of_mem
    change κ (p : R) = 0
    simpa only [map_natCast] using hp0

/-- 単元倍はperfectoidイデアルを変えない。 -/
theorem BhattScholze.Almost.perfectoidIdeal_mul_unit_eq (g a : R) (ha : IsUnit a) :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (g * a) = _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g := by
  have hs : Ideal.span {g * a} = Ideal.span {g} := Ideal.span_singleton_mul_right_unit ha g
  exact le_antisymm (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mono R p hR hs.le)
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mono R p hR hs.ge)

/-- perfectoidなpねじれ商があれば、p^c g'で消える射からg'のperfectoidイデアルの像はpねじれ。
商のperfectoid性を単にpの非零因子性から推論しない。 -/
theorem BhattScholze.Almost.perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hS : _root_.SerrePositivity.IsIntegralPerfectoid S p)
    (hQ : _root_.SerrePositivity.IsIntegralPerfectoid (S ⧸ _root_.SerrePositivity.pTorsionIdeal S p) p)
    (f : R →+* S) (g' : R) (c : ℕ) (hg : (p : S) ^ c * f g' = 0)
    (x : R) (hx : x ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g') : (p : S) * f x = 0 := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g'}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g')
  let q := Ideal.Quotient.mk (_root_.SerrePositivity.pTorsionIdeal S p)
  have hfg : g' ∈ RingHom.ker (q.comp f) := by
    change q (f g') = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hS.p_mul_eq_zero_of_pow_mul_eq_zero S p c (f g') hg)
  let k : R ⧸ Ideal.span {g'} →+* S ⧸ _root_.SerrePositivity.pTorsionIdeal S p :=
    Ideal.Quotient.lift _ (q.comp f) ((Ideal.span_singleton_le_iff_mem _).mpr hfg)
  let hu := _root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g'}) p hR
  have he := RingHom.congr_fun (_root_.SerrePositivity.IsPerfectoidization.lift_comp hu hQ k)
    (Ideal.Quotient.mk (Ideal.span {g'}) x)
  change _root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g'}) p hR
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
theorem BhattScholze.Almost.perfectoidIdeal_isRadical (g : R) :
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).IsRadical := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let T := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R (Ideal.span {g}) p hR
  let κ : R →+* T := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  have hT : _root_.SerrePositivity.IsIntegralPerfectoid T p :=
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).1
  let := hT.isReduced T p
  intro x hx
  obtain ⟨n, hn⟩ := hx
  change κ x = 0
  apply IsReduced.eq_zero
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact hn

/-- Every root of the original principal ideal lies in its perfectoid ideal. -/
theorem BhattScholze.Almost.radical_span_le_perfectoidIdeal (g : R) :
    (Ideal.span {g}).radical ≤ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g :=
  (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isRadical R p hR g).radical_le_iff.mpr
    (_root_.SerrePositivity.BhattScholze.Almost.span_le_perfectoidIdeal R p hR g)

/-- Positive powers of any element define the same perfectoid ideal.
No regularity of g or of p is required. -/
theorem BhattScholze.Almost.perfectoidIdeal_pow_eq (g : R) (n : ℕ) (hn : 0 < n) :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (g ^ n) = _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g := by
  apply le_antisymm
  · apply _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_mono
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn
  · apply _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_le_of_mem
    apply _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isRadical R p hR (g ^ n)
    exact ⟨n, (_root_.SerrePositivity.BhattScholze.Almost.span_le_perfectoidIdeal R p hR (g ^ n))
      (Ideal.subset_span (Set.mem_singleton _))⟩

end SerrePositivity

end PerfectoidIdealRadicalPart
