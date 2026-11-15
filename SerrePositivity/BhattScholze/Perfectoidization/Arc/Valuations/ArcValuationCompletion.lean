module

public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Reduced

/-!
# 階数 1 の付値環の完備化

## 概要
非零非単元 a に沿う完備化は階数 1 の付値環で、完備化への単位は忠実平坦。
標数 p で完全なら、完備化も完全。

## 方針
完備化の元を元の付値環から来る元の単元倍に書く。完全性は、剰余環の a の p 倍の指数から
逆 Frobenius を適用する両立族で示す。

## 規約
環の階数は Krull 次元で測る。

## 使われ方
BS 著者版 Proposition 8.10 の証明の試験付値環の完備化。
-/

@[expose] public noncomputable section

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.IsLocalRing

section

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

/-- 階数 1 の付値環で非単元の冪は任意の非零元で割り切れる。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_exists_dvd_pow (hV : ringKrullDim V = 1)
    {a b : V} (ha : ¬ IsUnit a) (hb : b ≠ 0) : ∃ n : ℕ, b ∣ a ^ n := by
  obtain ⟨n, hn⟩ := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hV).2 b hb
    ((mem_maximalIdeal a).mpr ha)
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

variable (a : V)
set_option quotPrecheck false in
local notation "I" => Ideal.span ({a} : Set V)
local notation "T" => AdicCompletion I V
local notation "f" => algebraMap V T

/-- 非零非単元に沿う完備化への単位は単射。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_completion_injective (hV : ringKrullDim V = 1)
    (ha : a ≠ 0) (hna : ¬ IsUnit a) : Function.Injective f := by
  have hfg : (I : Ideal V).FG := Submodule.fg_span_singleton a
  have hz (x : V) (hx : f x = 0) : x = 0 := by
    by_contra hn
    obtain ⟨n, c, hc⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_exists_dvd_pow hV hna hn
    have hm := (_root_.SerrePositivity.adicCompletion_algebraMap_mem_map_pow_iff I hfg (n + 1) x).mp
      (hx ▸ (Ideal.zero_mem _))
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
    obtain ⟨b, hb⟩ := hm
    have hmul : a ^ n * (a * (b * c)) = a ^ n * 1 := by
      calc
        a ^ n * (a * (b * c)) = a ^ (n + 1) * b * c := by rw [pow_succ]; ac_rfl
        _ = x * c := by rw [hb]
        _ = a ^ n * 1 := by rw [← hc, mul_one]
    exact hna (isUnit_iff_dvd_one.mpr ⟨b * c, (mul_left_cancel₀ (pow_ne_zero _ ha) hmul).symm⟩)
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

/-- 完備化の各元は元の環から来る元と単元倍の違いしかない。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_completion_associated (x : T) : ∃ r : V, Associated (f r) x := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  have hfg : (I : Ideal V).FG := Submodule.fg_span_singleton a
  have hex : ∃ n : ℕ, AdicCompletion.evalₐ I n x ≠ 0 := by
    by_contra! h
    exact hx (AdicCompletion.ext_evalₐ fun n => (h n).trans (map_zero _).symm)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.exists_adicCompletion_algebraMap_sub_mem I hfg (n + 1) x
  have hrn : ¬ a ^ n ∣ r := by
    intro h
    have h1 : f r ∈ (I ^ n).map f := (_root_.SerrePositivity.adicCompletion_algebraMap_mem_map_pow_iff I hfg n r).mpr
      (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton.mpr h)
    have h2 : f r - x ∈ (I ^ n).map f :=
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) hr
    have h3 : x ∈ (I ^ n).map f := by
      simpa using ((I ^ n).map f).sub_mem h1 h2
    rw [← _root_.SerrePositivity.adicCompletion_ker_eval_eq_map I hfg] at h3
    exact hn h3
  obtain ⟨b, hb⟩ := (ValuationRing.dvd_total r (a ^ n)).resolve_right hrn
  rw [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
    map_pow] at hr
  obtain ⟨c, hc⟩ := hr
  have hrep : x = f r * (f a * (- f b * c) + 1) := by
    have hpow : f a ^ n = f r * f b := by rw [← map_pow, hb, map_mul]
    rw [pow_succ, hpow] at hc
    calc
      x = f r - (f r - x) := by simp
      _ = f r * (f a * (- f b * c) + 1) := by rw [hc]; ring
  let J : Ideal T := Ideal.span {f a}
  have hJ : J = (I).map f := by rw [Ideal.map_span, Set.image_singleton]
  have hcT : IsAdicComplete J T := by
    rw [hJ]
    exact (IsAdicComplete.map_algebraMap_iff I T).mpr (AdicCompletion.isAdicComplete hfg)
  let := hcT
  have hmem : f a ∈ (⊥ : Ideal T).jacobson :=
    IsAdicComplete.le_jacobson_bot J (Ideal.subset_span (Set.mem_singleton _))
  have hu := (Ideal.mem_jacobson_bot.mp hmem) (- f b * c)
  exact ⟨r, (hrep.symm ▸ associated_mul_unit_right _ _ hu)⟩

/-- 非零非単元に沿う完備化は階数 1 の付値環。単位は局所単射で忠実平坦。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_completion (hV : ringKrullDim V = 1)
    (ha : a ≠ 0) (hna : ¬ IsUnit a) :
    ∃ hT : IsDomain T, @ValuationRing T _ hT ∧ ringKrullDim T = 1 ∧
      IsAdicComplete (Ideal.span {f a}) T ∧ RingHom.FaithfullyFlat f := by
  have hf := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_completion_injective a hV ha hna
  have hrep := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_completion_associated a
  have hfg : (I : Ideal V).FG := Submodule.fg_span_singleton a
  let : Nontrivial T := hf.nontrivial
  let : NoZeroDivisors T := ⟨fun {x y} hxy => by
      obtain ⟨r, hr⟩ := hrep x
      obtain ⟨s, hs⟩ := hrep y
      have h : f (r * s) = 0 := (hr.mul_mul hs).eq_zero_iff.mpr hxy |> (map_mul f r s ▸ ·)
      have h0 : r * s = 0 := hf (h.trans (map_zero f).symm)
      rcases mul_eq_zero.mp h0 with h | h
      · exact Or.inl (hr.eq_zero_iff.mp (by rw [h, map_zero]))
      · exact Or.inr (hs.eq_zero_iff.mp (by rw [h, map_zero]))⟩
  let hT : IsDomain T := NoZeroDivisors.to_isDomain T
  let hVT : ValuationRing T := ValuationRing.iff_dvd_total.mpr ⟨fun x y => by
    obtain ⟨r, hr⟩ := hrep x
    obtain ⟨s, hs⟩ := hrep y
    rcases ValuationRing.dvd_total r s with h | h
    · exact Or.inl (hs.dvd_iff_dvd_right.mp (hr.dvd_iff_dvd_left.mp (map_dvd f h)))
    · exact Or.inr (hr.dvd_iff_dvd_right.mp (hs.dvd_iff_dvd_left.mp (map_dvd f h)))⟩
  have hI : (I : Ideal V) ≤ maximalIdeal V :=
    (Ideal.span_singleton_le_iff_mem _).mpr ((mem_maximalIdeal a).mpr hna)
  let g : T →+* ResidueField V :=
    (Ideal.Quotient.factor hI).comp (AdicCompletion.evalOneₐ I).toRingHom
  let : IsLocalHom f := ⟨fun x hx => by
    have hres : g (f x) = residue V x := by
      change (Ideal.Quotient.factor hI)
        (((AdicCompletion.evalOneₐ I).toRingHom.comp f) x) = _
      rw [AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
      rfl
    by_contra hn
    have hz := (residue_eq_zero_iff x).mpr ((mem_maximalIdeal x).mpr hn)
    exact not_isUnit_zero (hres.trans hz ▸ hx.map g)⟩
  refine ⟨hT, hVT, ?_, ?_, ?_⟩
  · apply ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mpr
    refine ⟨fun h => hna (IsUnit.of_map f a ?_), ?_⟩
    · obtain ⟨b, hb⟩ := h.mul_inv_cancel (a := f a)
        (fun h0 => ha (hf (h0.trans (map_zero f).symm)))
      exact isUnit_iff_dvd_one.mpr ⟨b, hb.symm⟩
    · intro x hx y hy
      obtain ⟨r, hr⟩ := hrep x
      obtain ⟨s, hs⟩ := hrep y
      have hr0 : r ≠ 0 := fun h => hx (hr.eq_zero_iff.mp (by rw [h, map_zero]))
      have hsu : ¬ IsUnit s := fun h => ((mem_maximalIdeal y).mp hy) (hs.isUnit (h.map f))
      obtain ⟨n, hn⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_exists_dvd_pow hV hsu hr0
      apply Ideal.mem_radical_iff.mpr
      refine ⟨n, Ideal.mem_span_singleton.mpr ?_⟩
      apply (hr.dvd_iff_dvd_left).mp
      apply ((hs.pow_pow (n := n)).dvd_iff_dvd_right).mp
      simpa only [map_pow] using map_dvd f hn
  · have h := (IsAdicComplete.map_algebraMap_iff (S := T) I T).mpr
      (AdicCompletion.isAdicComplete hfg)
    simpa only [Ideal.map_span, Set.image_singleton] using h
  · apply RingHom.faithfullyFlat_algebraMap_iff.mpr
    let : Module.IsTorsionFree V T := Module.isTorsionFree_iff_algebraMap_injective.mpr hf
    let : Module.Flat V T := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom

section PerfectCompletion

variable (p : ℕ) [Fact p.Prime] [CharP V p] [PerfectRing V p]

omit [IsDomain V] [ValuationRing V] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completion_evalₐ_factor {m n : ℕ} (hmn : m ≤ n) (x : T) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I V x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (s n) = Ideal.Quotient.mk (I ^ m) (s m)
  apply Ideal.Quotient.eq.mpr
  simpa [SModEq.sub_mem, Ideal.mul_top] using (s.property hmn).symm

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel (n : ℕ) : (V ⧸ I ^ (p * n)) →+* (V ⧸ I ^ n) := by
  let g := (frobeniusEquiv V p).symm.toRingHom
  refine Ideal.quotientMap _ g ?_
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
    pow_mul, map_pow]
  have hg : g (a ^ p) = a := (frobeniusEquiv V p).symm_apply_apply a
  rw [hg, Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

omit [IsDomain V] [ValuationRing V] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel_mk (n : ℕ) (x : V) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel a p n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ ((frobeniusEquiv V p).symm x) := rfl

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap (n : ℕ) : T →+* (V ⧸ I ^ n) :=
  (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel a p n).comp (AdicCompletion.evalₐ I (p * n)).toRingHom

omit [IsDomain V] [ValuationRing V] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap_compat {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap a p n) =
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap a p m := by
  ext x : 1
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (p * n) x)
  have hr' : Ideal.Quotient.mk (I ^ (p * m)) r = AdicCompletion.evalₐ I (p * m) x := by
    have hmn' := Nat.mul_le_mul_left p hmn
    exact (congrArg (Ideal.Quotient.factorPow I hmn') hr).trans (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completion_evalₐ_factor a hmn' x)
  change Ideal.Quotient.factorPow I hmn (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel a p n (AdicCompletion.evalₐ I _ x)) =
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel a p m (AdicCompletion.evalₐ I _ x)
  rw [← hr, ← hr', _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel_mk, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel_mk]
  rfl

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius : T →+* T :=
  AdicCompletion.liftRingHom I (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap a p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap_compat a p)

omit [IsDomain V] [ValuationRing V] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius_eval (n : ℕ) (x : T) :
    AdicCompletion.evalₐ I n (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius a p x) =
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel a p n (AdicCompletion.evalₐ I (p * n) x) := by
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius
  exact AdicCompletion.evalₐ_liftRingHom I
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap a p) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootMap_compat a p) n x

end PerfectCompletion

end

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius_pow {V : Type*} [CommRing V] [IsDomain V]
    [ValuationRing V] (a : V) (p : ℕ) [Fact p.Prime] [CharP V p] [PerfectRing V p]
    (x : AdicCompletion (Ideal.span {a}) V) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius a p x ^ p = x := by
  let I := Ideal.span {a}
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [map_pow]
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius_eval]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (p * n) x)
  have hn : n ≤ p * n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n (Fact.out : p.Prime).one_lt.le
  change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel a p n (AdicCompletion.evalₐ I (p * n) x) ^ p =
    AdicCompletion.evalₐ I n x
  rw [← hr, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRootLevel_mk, ← map_pow]
  change Ideal.Quotient.mk (I ^ n) ((frobeniusEquiv V p) ((frobeniusEquiv V p).symm r)) =
    AdicCompletion.evalₐ I n x
  rw [RingEquiv.apply_symm_apply]
  exact (congrArg (Ideal.Quotient.factorPow I hn) hr).trans (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completion_evalₐ_factor a hn x)

universe u

/-- 階数 1 の完全付値環の非零非単元に沿う完備化。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcValuation_completeAt (p : ℕ) [Fact p.Prime] [Fact p.Prime]
    (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [CharP V p] [PerfectRing V p] (hV : ringKrullDim V = 1)
    (a : V) (ha : a ≠ 0) (hna : ¬ IsUnit a) :
    let T := AdicCompletion (Ideal.span {a}) V
    let e := algebraMap V T
    ∃ hT : IsDomain T, @ValuationRing T _ hT ∧ ringKrullDim T = 1 ∧
      CharP T p ∧ PerfectRing T p ∧ IsAdicComplete (Ideal.span {e a}) T ∧ e.FaithfullyFlat := by
  let T := AdicCompletion (Ideal.span {a}) V
  let f := algebraMap V T
  obtain ⟨hT, hval, hdim, hcomp, hflat⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_completion a hV ha hna
  let := hT
  let hchar : CharP T p :=
    charP_of_injective_ringHom (f := f) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rankOneValuation_completion_injective a hV ha hna) p
  have hF : PerfectRing T p := ⟨⟨frobenius_inj T p, fun x =>
    ⟨_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius a p x, _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionInverseFrobenius_pow a p x⟩⟩⟩
  exact ⟨hT, hval, hdim, hchar, hF, hcomp, hflat⟩

end SerrePositivity.BhattScholze.Perfectoidization.Derived
