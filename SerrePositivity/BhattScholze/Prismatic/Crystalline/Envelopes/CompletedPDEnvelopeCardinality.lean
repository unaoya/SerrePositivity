module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDEnvelopeCardinality
public import SerrePositivity.CommutativeAlgebra.Adic.Cardinality
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
public import Mathlib.Algebra.MvPolynomial.Cardinal
import all SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.CompletedPDEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve

/-!
# 完備分冪包と Čech 項の cutoff

## 概要
未完備包の濃度評価と完備化の可算冪の評価を組み合わせる。

## 方針
多項式枠の濃度を最初の無限基数で抑え、一度だけ可算冪を取る。

## 規約
任意の κ について κ^ℵ₀=κ を仮定せず、最後に cutoff ≤ κ を使う。
枠の変数の濃度は #k+#R+ℵ₀ で抑える。

## 使われ方
Berthelot I.2.3.1、III.4、Stacks 07HP。実際の pd Čech の塔が cutoff 内に残ること。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open scoped Cardinal
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J)

/-- 完備分冪包の濃度は入力環を抑える無限基数の可算冪以下。 -/
theorem completedPDEnvelope_cardinal_le_power {B : Type u} [CommRing B] [Algebra k B]
    (K : Ideal B) (hK : J.map (algebraMap k B) ≤ K)
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hB : Cardinal.mk B ≤ κ) :
    Cardinal.mk (completedPDEnvelope p γ hp K hK).carrier ≤ κ ^ ℵ₀ := by
  change Cardinal.mk (AdicCompletion (Ideal.span {(p : RelativePDEnvelope.Ring γ K)})
    (RelativePDEnvelope.Ring γ K)) ≤ κ ^ ℵ₀
  exact (SerrePositivity.adicCompletion_cardinal_le (M := RelativePDEnvelope.Ring γ K) _).trans
    (Cardinal.power_le_power_right
      (PDEnvelopeCardinality.relativePDEnvelope_cardinal_le K γ κ hκ hB))

/-- 同じ無限濃度で基底と枠の変数を抑えれば、各 Čech 項はその可算冪以下。 -/
theorem pdCechTerm_cardinal_le_power {R : Type u} [CommRing R] [Algebra k R]
    (hJ : J ≤ RingHom.ker (algebraMap k R)) {S : Type u} (s : S → R)
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hk : Cardinal.mk k ≤ κ) (hS : Cardinal.mk S ≤ κ)
    (n : ℕ) : Cardinal.mk (PDCechNerve.term p γ hp hJ s n).carrier ≤ κ ^ ℵ₀ := by
  have hF : Cardinal.lift.{u} (Cardinal.mk (Fin (n + 1))) ≤ κ :=
    (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0).trans hκ
  have hvars : Cardinal.mk (S × Fin (n + 1)) ≤ κ := by
    simpa only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_uzero] using
      (mul_le_mul' hS hF).trans (Cardinal.mul_eq_self hκ).le
  have hframe : Cardinal.mk (pdFrame k S n) ≤ κ :=
    MvPolynomial.cardinalMk_le_max.trans (sup_le (sup_le hk hvars) hκ)
  unfold PDCechNerve.term
  exact completedPDEnvelope_cardinal_le_power p γ hp _
    (PDCechNerve.base_le_ker hJ s n) κ hκ hframe

/-- 標準の cutoff より小さい基数で枠を抑え、分冪 Čech の全項を cutoff 内に置く。 -/
theorem pdCechTerm_cardinal_le_cutoff {R : Type u} [CommRing R] [Algebra k R]
    (hJ : J ≤ RingHom.ker (algebraMap k R)) {S : Type u} (s : S → R)
    (hS : Cardinal.mk S ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀) (n : ℕ) :
    Cardinal.mk (PDCechNerve.term p γ hp hJ s n).carrier ≤ cutoff k R := by
  let μ : Cardinal.{u} := Cardinal.mk k + Cardinal.mk R + ℵ₀
  have hμ : ℵ₀ ≤ μ := self_le_add_left _ _
  have hk : Cardinal.mk k ≤ μ := (self_le_add_right _ _).trans (self_le_add_right _ _)
  exact pdCechTerm_cardinal_le_power p γ hp hJ s μ hμ hk hS n

/-- cutoff の上限 κ について、同じ枠の Čech 項の濃度条件を供給する。 -/
theorem pdCechTerm_cardinal_le_of_cutoff {R : Type u} [CommRing R] [Algebra k R]
    (hJ : J ≤ RingHom.ker (algebraMap k R)) {S : Type u} (s : S → R)
    (hS : Cardinal.mk S ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀)
    {κ : Cardinal.{u}} (hκ : IsCrystallineCutoff k R κ) (n : ℕ) :
    Cardinal.mk (PDCechNerve.term p γ hp hJ s n).carrier ≤ κ :=
  (pdCechTerm_cardinal_le_cutoff p γ hp hJ s hS n).trans hκ

end SerrePositivity.BhattScholze.Prismatic
