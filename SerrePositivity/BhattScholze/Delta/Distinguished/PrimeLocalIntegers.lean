module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# p 局所整数環の δ 構造

## 概要
BS 著者版 §2 の係数環 ℤ₍ₚ₎ に標準 δ 構造を与える。

## 方針
整数の恒等 Frobenius から δ 構造を作り、素数 p で局所化する。

## 規約
p 進完備化の前の局所環。

## 使われ方
自由 δ 環の分冪包と普遍 distinguished 環。
-/

public noncomputable section

namespace SerrePositivity.BhattScholze

variable (p : ℕ) [Fact p.Prime]

local notation "I" => Ideal.span {(p : ℤ)}

private theorem integerFrobenius_exists :
    ∃! D : DeltaStructure p ℤ, D.frobeniusLift = RingHom.id ℤ := by
  apply DeltaStructure.existsUnique_of_frobeniusLift
  · have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    intro a b hab
    exact mul_left_cancel₀ hp hab
  · intro x
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    change ((x - x^p : ℤ) : ZMod p) = 0
    rw [Int.cast_sub, Int.cast_pow, ZMod.pow_card, sub_self]

private def integerDelta : DeltaStructure p ℤ := (integerFrobenius_exists p).choose

private theorem integerDelta_stable (s : (I).primeCompl) :
    (integerDelta p).frobeniusLift s ∈ (I).primeCompl := by
  rw [show (integerDelta p).frobeniusLift = RingHom.id ℤ from
    (integerFrobenius_exists p).choose_spec.1]
  exact s.property

/-- 概要：p 局所な整数環 ℤ₍ₚ₎。
方針：素イデアル (p) の補集合で整数を局所化する。
規約：BS 著者版 §2 の係数。
使われ方：自由 δ 環の初期係数環。 -/
abbrev PrimeLocalInt := Localization.AtPrime I

/-- 概要：ℤ₍ₚ₎ 上の標準 δ 構造。
方針：整数の標準 δ 構造を、Frobenius 安定な分母で局所化する。
規約：BS 著者版 Example 2.6 の初期 δ 環。
使われ方：自由 δ 環と普遍 distinguished 環。 -/
def primeLocalIntDelta : DeltaStructure p (PrimeLocalInt p) :=
  (integerDelta p).localization (I).primeCompl _ (integerDelta_stable p)

/-- 概要：p と互いに素な自然数は ℤ₍ₚ₎ の単元。
方針：(p) に属さない元は局所化で可逆となる。
規約：BS 著者版 §2。
使われ方：分冪の階乗分母の計算。 -/
theorem primeLocalInt_isUnit (m : ℕ) (hm : ¬p ∣ m) :
    IsUnit (m : PrimeLocalInt p) := by
  have hn : (m : ℤ) ∈ (I).primeCompl := by
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]
    exact hm
  simpa only [map_natCast] using
    (IsLocalization.map_units (PrimeLocalInt p) (⟨(m : ℤ), hn⟩ : (I).primeCompl))

/-- 概要：ℤ₍ₚ₎ の mod p は素数体。
方針：素イデアルでの局所化が剰余体を保つことと整数の mod p を使う。
規約：BS 著者版 Lemma 2.36 と Example 2.21。
使われ方：自由 δ 環の Frobenius の完全平坦性。 -/
def primeLocalIntModPrimeEquiv :
    ((PrimeLocalInt p) ⧸ Ideal.span {(p : PrimeLocalInt p)}) ≃+* ZMod p := by
  have h : Ideal.span {(p : PrimeLocalInt p)} = IsLocalRing.maximalIdeal (PrimeLocalInt p) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal I (PrimeLocalInt p), Ideal.map_span,
      Set.image_singleton, map_natCast]
  exact (Ideal.quotEquivOfEq h).trans
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal I (PrimeLocalInt p)).symm.toRingEquiv.trans
      (Int.quotientSpanNatEquivZMod p))

/-- 概要：ℤ₍ₚ₎ から p 局所な δ 環への標準 δ 射が一意。
方針：整数の δ 射性は長さ二の Witt 切断の図式と整数の初期性から従う。
規約：BS 著者版 Example 2.6 の初期 δ 環。
使われ方：自由 δ 環からの評価。 -/
theorem existsUnique_primeLocalIntDeltaHom {A : Type*} [CommRing A] (D : DeltaStructure p A)
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    ∃! f : PrimeLocalInt p →+* A, (primeLocalIntDelta p).IsDeltaHom D f := by
  let φ : ℤ →+* A := Int.castRingHom A
  have hφ : (integerDelta p).IsDeltaHom D φ :=
    ((integerDelta p).isDeltaHom_iff_sectionHom_comp D φ).mpr (Subsingleton.elim _ _)
  obtain ⟨g, hg, hu⟩ := (integerDelta p).existsUnique_localization_lift
    (I).primeCompl (PrimeLocalInt p) (integerDelta_stable p) D φ hφ (by
      intro z
      have hz := (Ideal.mem_primeCompl_iff.mp z.property)
      rw [Ideal.mem_span_singleton] at hz
      cases h : (z : ℤ) with
      | ofNat m =>
          rw [h] at hz
          change ¬(p : ℤ) ∣ (m : ℤ) at hz
          rw [Int.natCast_dvd_natCast] at hz
          change IsUnit (((m : ℕ) : ℤ) : A)
          simpa only [Int.cast_natCast] using hA m hz
      | negSucc m =>
          have hn : ¬p ∣ m+1 := by
            intro hh
            apply hz
            rw [h, Int.negSucc_eq, dvd_neg]
            exact_mod_cast hh
          change IsUnit ((Int.negSucc m : ℤ) : A)
          simpa only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one] using (hA (m+1) hn).neg)
  exact ⟨g, hg.2, fun f hf => hu f ⟨Subsingleton.elim _ _, hf⟩⟩

end SerrePositivity.BhattScholze

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 2.6" (partial := special) "最後の主張（p 冪零な δ 環は零環）と Z 上の δ 構造の一意性の形だけ。Z_(p)（Lean は p と互いに素な整数での局所化）が δ 環の始対象であることは公開の existsUnique_primeLocalIntDeltaHom（Ex 2.21 の構成で使う） ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：relativeFreeDeltaStructure_int_eq（Z 上の二構成の一致で、Z_(p) の始性や δ 構造の一意性を主張する型ではない。） ／ DOC1 照合：ok 1 件 ／ 11-12 夜更新（ノート本文の更新時）。ℤ 上の δ 構造の存在と一意性は非公開の補題だけ"] _root_.SerrePositivity.BhattScholze.existsUnique_primeLocalIntDeltaHom
