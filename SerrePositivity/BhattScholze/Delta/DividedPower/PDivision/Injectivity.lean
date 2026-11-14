module
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.OreLocalization.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Algebra.Defs

public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.AdicCompletion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.HomologicalAlgebra.SequentialComplexColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# p 正則な除算包の局所化への単射

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v

/-! ## 最初のδ像を加えたp除算関係商のp正則性

指定した一つの関係とその最初のδ像を扱う。全δ閉包への移行は別工程。
-/

@[expose] public noncomputable section DeltaPDivisionRawEmbedding

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section General
variable {σ : Type v} (D : DeltaStructure p A) (a : σ → A)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a
local notation "Bₚ" => Localization.Away (p : B₀)

/-- raw包がp正則なら、具体的δ評価B→A[1/p]は単射。 -/
theorem deltaPDivisionToAway_injective_of_p_mul_injective
    (hp : Function.Injective (fun x : B₀ ↦ (p : B₀) * x)) :
    Function.Injective (deltaPDivisionToAway D a) := by
  have hj : Function.Injective (algebraMap B₀ Bₚ) := by
    intro x z hxz
    have hzero : algebraMap B₀ Bₚ (x - z) = 0 := by rw [map_sub, hxz, sub_self]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (p : B₀)) Bₚ (x - z)).mp hzero
    obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff (m : B₀) (p : B₀)).mp m.property
    have hreg : IsLeftRegular (p : B₀) := by
      intro t w htw
      exact hp htw
    apply sub_eq_zero.mp
    apply hreg.pow N
    change (p : B₀) ^ N * (x - z) = (p : B₀) ^ N * 0
    rw [hN, hm, mul_zero]
  intro x z hxz
  apply hj
  calc
    algebraMap B₀ Bₚ x = deltaPDivisionAwayToAway D a (deltaPDivisionToAway D a x) :=
      (RingHom.congr_fun (deltaPDivisionAwayToAway_comp_toAway D a) x).symm
    _ = deltaPDivisionAwayToAway D a (deltaPDivisionToAway D a z) := congrArg _ hxz
    _ = algebraMap B₀ Bₚ z := RingHom.congr_fun (deltaPDivisionAwayToAway_comp_toAway D a) z

end General

end SerrePositivity.BhattScholze

end DeltaPDivisionRawEmbedding

/-! ## 正則一元raw包と具体的階乗生成部分環の標準同型

単射性の中間仮定を明示する。導来pushout比較・分冪包普遍性は別工程。
-/

