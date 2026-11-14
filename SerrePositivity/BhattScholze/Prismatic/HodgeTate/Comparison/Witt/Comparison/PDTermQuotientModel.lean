module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelCompletionQuotient
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison

/-!
# 小さい完備分冪模型の有限冪商

## 概要
完備分冪模型の実際の各項を p の冪で割り、未完備項の商と比較する。

## 方針
p 正則性から主完備化の H⁰ を古典的完備化と照合し、その後に有限冪商を取る。

## 規約
商は p^e で生成される主イデアルによる。

## 使われ方
BS 著者版 Theorem 6.4 の係数変更。
-/

public noncomputable section

open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ)
variable (hr : Function.Injective (fun x : k => (p : k) * x))

local notation "Raw" => pdRaw k r n
local notation "Term" => pdTerm p k r n
local notation "I" => Ideal.span {(p : Raw)}
local notation "Comp" => AdicCompletion I Raw

private def eTerm : Term ≃+* Comp :=
  PDSmallModelComparison.principalAdicRingEquiv Raw (p : Raw)
    (PDSmallRawEnvelope.raw_regular p r n hr)

private theorem eTerm_unit (x : Raw) :
    eTerm p k r n hr (principalCompletionRingCatUnit p (CommRingCat.of Raw) x) =
      algebraMap Raw Comp x :=
  PDSmallModelComparison.principalAdicRingEquiv_unit Raw (p : Raw)
    (PDSmallRawEnvelope.raw_regular p r n hr) x

/-- 完備項の有限冪商は未完備項の同じ有限冪商で表される。 -/
def pdTermQuotientEquiv (e : ℕ) :
    (Term ⧸ Ideal.span {(p : Term) ^ e}) ≃+* (Raw ⧸ Ideal.span {(p : Raw) ^ e}) := by
  let a := eTerm p k r n hr
  have h : (Ideal.map (algebraMap Raw Comp) I) ^ e =
      (Ideal.span {(p : Term) ^ e}).map a.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_pow,
      Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  exact (Ideal.quotientEquiv _ _ a h).trans
    ((adicCompletionPowQuotientEquiv I (Submodule.fg_span_singleton _) e).toRingEquiv.trans
      (Ideal.quotEquivOfEq (Ideal.span_singleton_pow (p : Raw) e)))

theorem pdTermQuotientEquiv_unit (e : ℕ) (x : Raw) :
    pdTermQuotientEquiv p k r n hr e
      (Ideal.Quotient.mk _ (principalCompletionRingCatUnit p (CommRingCat.of Raw) x)) =
        Ideal.Quotient.mk _ x := by
  unfold pdTermQuotientEquiv
  simp only [RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  have hu := eTerm_unit p k r n hr x
  rw [hu]
  have h := adicCompletionPowQuotientEquiv_algebraMap I (Submodule.fg_span_singleton _) e x
  rw [show (adicCompletionPowQuotientEquiv I (Submodule.fg_span_singleton _) e).toRingEquiv
    (Ideal.Quotient.mk _ (algebraMap Raw Comp x)) = Ideal.Quotient.mk _ x from h]
  rfl

end SerrePositivity.BhattScholze.Prismatic
