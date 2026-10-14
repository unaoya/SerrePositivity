module

public import SerrePositivity.BhattScholze.DeltaFrobenius
public import SerrePositivity.BhattScholze.PerfectDeltaModP
public import Mathlib.RingTheory.WittVector.Complete

/-! # 完全な標数p環のWitt環のδ構造

BS著者公開版Corollary 2.31の(3)から(1)。MathlibのWitt Frobenius、
p正則性・完備性を再利用して一意なδ構造を与える。圏同値全体はまだ構成しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- Witt Frobeniusを持ち上げとするδ構造の存在・一意性。
Witt環のp正則性とmod pの第0座標公式を既存Mathlibから供給する。 -/
theorem existsUnique_wittDeltaStructure :
    ∃! D : DeltaStructure p (WittVector p k), D.frobeniusLift = WittVector.frobenius := by
  have hp : Function.Injective (fun x : WittVector p k ↦ (p : WittVector p k) * x) := by
    intro x y hxy
    change (p : WittVector p k) * x = (p : WittVector p k) * y at hxy
    apply sub_eq_zero.mp
    apply WittVector.eq_zero_of_p_mul_eq_zero
    rw [mul_comm, mul_sub, hxy, sub_self]
  apply DeltaStructure.existsUnique_of_frobeniusLift hp WittVector.frobenius
  intro x
  apply Ideal.mem_span_singleton.mp
  apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
  change (WittVector.constantCoeff : WittVector p k →+* k)
    (WittVector.frobenius x - x ^ p) = 0
  rw [map_sub, map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.coeff_frobenius_charP, sub_self]

/-- 完全な標数p環のWitt環の標準δ構造。Frobenius持上げから一意に選ぶ。 -/
def wittDeltaStructure : DeltaStructure p (WittVector p k) :=
  (existsUnique_wittDeltaStructure p k).choose

/-- 標準Witt δ構造のFrobenius持上げはMathlibのWitt Frobenius。 -/
@[simp] theorem wittDeltaStructure_frobeniusLift :
    (wittDeltaStructure p k).frobeniusLift = WittVector.frobenius :=
  (existsUnique_wittDeltaStructure p k).choose_spec.1

/-- 標準Witt δ構造は完全。MathlibのWitt Frobenius同型を使う。 -/
theorem wittDeltaStructure_isPerfect : (wittDeltaStructure p k).IsPerfect := by
  change Function.Bijective (wittDeltaStructure p k).frobeniusLift
  rw [wittDeltaStructure_frobeniusLift]
  exact WittVector.frobenius_bijective p k

/-- 標準Witt δ環はp進完備。新しい完備性モデルを導入せずMathlibのインスタンスを返す。 -/
theorem wittDeltaStructure_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := inferInstance

/-- 同じWitt Frobeniusを持つδ構造は標準構造に一致する。 -/
theorem wittDeltaStructure_unique (D : DeltaStructure p (WittVector p k))
    (hD : D.frobeniusLift = WittVector.frobenius) : D = wittDeltaStructure p k :=
  (existsUnique_wittDeltaStructure p k).choose_spec.2 D hD

/-- 完全な標数p環の間の写像が誘導するWitt写像は標準δ構造と可換。
Witt Frobeniusの座標公式と、終域のp正則性によるδの復元を使う。 -/
theorem wittDeltaStructure_map_isDeltaHom {l : Type v} [CommRing l] [CharP l p]
    [PerfectRing l p] (f : k →+* l) :
    (wittDeltaStructure p k).IsDeltaHom (wittDeltaStructure p l) (WittVector.map f) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift
  · exact (wittDeltaStructure_isPerfect p l).p_mul_injective
  · intro x
    rw [wittDeltaStructure_frobeniusLift, wittDeltaStructure_frobeniusLift]
    apply WittVector.ext
    intro n
    simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

end SerrePositivity.BhattScholze
