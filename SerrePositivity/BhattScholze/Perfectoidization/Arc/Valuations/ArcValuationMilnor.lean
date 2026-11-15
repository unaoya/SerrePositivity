module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.FieldTheory.Perfect

/-!
# 付値環の Milnor 短完全列

## 概要
任意の付値環と素イデアルに対し、局所化と商からなる Milnor 短完全列を構成する。

## 方針
素イデアルの局所化において、剰余が零の分数は分母で割り切れ、元の素イデアルから来る。

## 規約
完全性は加法群の列で述べる。

## 使われ方
BS 著者版 Proposition 8.10 の証明と、完全環上の Čech 降下。
-/

@[expose] public noncomputable section

universe u
open scoped _root_.nonZeroDivisors

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

variable (p : ℕ) [Fact p.Prime]

/-- 加法群としての付値環の Milnor 短完全列。最後の射は二つの剰余の差。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.MilnorShortExact {V : Type u} [CommRing V] (P : Ideal V) [P.IsPrime] : Prop :=
  let L := Localization.AtPrime P
  let i := fun x : V => (algebraMap V L x, Ideal.Quotient.mk P x)
  let d := fun z : L × (V ⧸ P) => IsLocalRing.residue L z.1 - algebraMap (V ⧸ P) P.ResidueField z.2
  Function.Injective i ∧ Function.Exact i d ∧ Function.Surjective d

/-- 任意の付値環 V と素イデアル 𝔭 に対し、加法群の列
`0 → V → V_𝔭 ⊕ V/𝔭 → κ(𝔭) → 0` は完全。
核の分数 a/s について、a ∈ 𝔭 と s ∉ 𝔭 から s ∣ a が従い、商も 𝔭 に入る。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    (𝔭 : Ideal V) [𝔭.IsPrime] : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.MilnorShortExact 𝔭 := by
  classical
  let L := Localization.AtPrime 𝔭
  let f : V →+* L := algebraMap V L
  let q : L →+* 𝔭.ResidueField := IsLocalRing.residue L
  have hkernel (x : L) (hx : q x = 0) : ∃ a : V, a ∈ 𝔭 ∧ f a = x := by
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl x
    have ha : a ∈ 𝔭 := (IsLocalization.AtPrime.mk'_mem_maximal_iff L 𝔭 a s).mp
      ((IsLocalRing.residue_eq_zero_iff _).mp hx)
    rcases ValuationRing.dvd_total (s : V) a with ⟨b, hb⟩ | ⟨b, hb⟩
    · have hbmem : b ∈ 𝔭 := ((inferInstance : 𝔭.IsPrime).mem_or_mem (hb ▸ ha)).resolve_left s.2
      refine ⟨b, hbmem, ?_⟩
      exact (IsLocalization.eq_mk'_iff_mul_eq.mpr (by rw [hb, map_mul, mul_comm]))
    · exact (s.2 (hb ▸ 𝔭.mul_mem_right b ha)).elim
  have hf : Function.Injective f :=
    IsLocalization.injective L (M := 𝔭.primeCompl) (fun a ha =>
      mem_nonZeroDivisors_iff_ne_zero.mpr (fun hz => ha (hz ▸ 𝔭.zero_mem)))
  have hcomm (a : V) :
      q (f a) = algebraMap (V ⧸ 𝔭) 𝔭.ResidueField (Ideal.Quotient.mk 𝔭 a) := rfl
  refine ⟨fun _ _ h => hf (congrArg Prod.fst h), ?_, ?_⟩
  · rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · intro h
      have hsub : q (x - f a) = 0 := by
        rw [map_sub, hcomm]
        exact h
      obtain ⟨b, hb, hbx⟩ := hkernel (x - f a) hsub
      refine ⟨b + a, Prod.ext ?_ ?_⟩
      · change f (b + a) = x
        rw [map_add, hbx, sub_add_cancel]
      · change Ideal.Quotient.mk 𝔭 (b + a) = Ideal.Quotient.mk 𝔭 a
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add]
    · rintro ⟨b, h⟩
      have hx : f b = x := congrArg Prod.fst h
      have hy : Ideal.Quotient.mk 𝔭 b = Ideal.Quotient.mk 𝔭 a := congrArg Prod.snd h
      change q x - algebraMap (V ⧸ 𝔭) 𝔭.ResidueField (Ideal.Quotient.mk 𝔭 a) = 0
      rw [← hx, ← hy, hcomm, sub_self]
  · intro z
    obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := L) z
    exact ⟨(x, 0), by simpa using hx⟩

/-- 完全付値環の場合の Milnor 短完全列（Bhatt–Scholze, [BS17, Lemma 6.3]）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare_perfect {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CharP V p] [PerfectRing V p]
    (𝔭 : Ideal V) [𝔭.IsPrime] : _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.MilnorShortExact 𝔭 := by
  exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare 𝔭

end SerrePositivity.BhattScholze.Perfectoidization.Derived
