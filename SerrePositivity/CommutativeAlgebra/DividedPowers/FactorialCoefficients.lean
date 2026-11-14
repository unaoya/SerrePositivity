module
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.Localization.Rat
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# p 局所化上の有理数作用

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u

/-! ## BS 著者版 Lemma 2.36の分冪展開係数のp可積分性

著者公開版p.23の係数をpで割った値について、既存p進付値で評価する。
分冪生成部分環のδ安定性への数論的入力。
-/

@[expose] public noncomputable section DeltaDividedPowers

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p局所環のp局所化では、非零自然数の像は単元。 -/
theorem primeDividedPowersAwayNat_isUnit
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (n : ℕ) (hn : n ≠ 0) :
    IsUnit (n : Localization.Away (p : A)) := by
  obtain ⟨k, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
  have hp : IsUnit (p : Localization.Away (p : A)) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (p : A)) (p : A)
  have hm' : IsUnit (m : Localization.Away (p : A)) := by
    simpa only [map_natCast] using (hlocal m hm).map (algebraMap A (Localization.Away (p : A)))
  rw [he, Nat.cast_mul, Nat.cast_pow]
  exact (hp.pow k).mul hm'

/-- p局所環のp局所化に、既存の有理数の局所化普遍性で与えるℚ作用。 -/
@[instance_reducible] def primeDividedPowersAwayRatAlgebra
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    Algebra ℚ (Localization.Away (p : A)) := by
  let L := Localization.Away (p : A)
  have hZ : ∀ z : nonZeroDivisors ℤ, IsUnit (Int.castRingHom L z) := by
    intro z
    have hz : (z : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp z.property
    rcases z with ⟨z, hz'⟩
    cases z with
    | ofNat n =>
        change (Int.ofNat n) ≠ 0 at hz
        exact primeDividedPowersAwayNat_isUnit hlocal n (fun hn ↦ hz (congrArg Int.ofNat hn))
    | negSucc n =>
        change IsUnit (-(n + 1 : L))
        exact (primeDividedPowersAwayNat_isUnit hlocal (n + 1) (Nat.succ_ne_zero n)).neg
  exact (IsLocalization.lift (S := ℚ) hZ).toAlgebra

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaDividedPowers

/-! ## 分冪展開のp可積分係数の実基底像

既約分母の単元逆数をA内で取り、標準局所化像の式を証明する。
ℚ作用は前工程の既存のものを用いる。p正則性は不要。
-/

