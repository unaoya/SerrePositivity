module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawBaseChangeLinear
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
import all SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic

/-!
# 小さい分冪模型の完備化と有限冪の商

## 概要
未完備の各項の自由基底を使って、完備化の有限冪商を未完備項の商で計算する。

## 方針
有限生成な主イデアルに対する完備化の商の比較を適用する。
さらに p 正則なとき、主導来完備化の H⁰ と古典的完備化を照合する。

## 規約
平坦性は各有限冪商について述べる。完備化そのものには平坦性を課さない。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 係数からの導来 p 完備底変換。
-/

public noncomputable section

open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ)

local notation "Raw" => pdRaw k r n
local notation "I" => Ideal.span {(p : k)}
local notation "J" => Ideal.map (algebraMap k Raw) I

private theorem pdRaw_adicIdeal : J = Ideal.span {(p : Raw)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- 小さい分冪模型の古典的完備化の有限冪商を未完備項の商で計算する。 -/
def pdRawCompletionQuotient (e : ℕ) :
    let B := AdicCompletion J Raw
    (B ⧸ ((I ^ e).map (algebraMap k B))) ≃ₐ[k ⧸ (I ^ e)]
      (Raw ⧸ ((I ^ e).map (algebraMap k Raw))) :=
  adicCompletionBasePowQuotientEquiv (S := Raw) I (Submodule.fg_span_singleton _) e

/-- 有限冪商の比較は未完備項からの標準射と両立する。 -/
theorem pdRawCompletionQuotient_unit (e : ℕ) (x : Raw) :
    pdRawCompletionQuotient p k r n e
      (Ideal.Quotient.mk _ (algebraMap Raw (AdicCompletion J Raw) x)) =
      Ideal.Quotient.mk _ x := by
  let B := AdicCompletion J Raw
  let hI : (I : Ideal k).FG := Submodule.fg_span_singleton _
  have hC : (Ideal.map (algebraMap Raw B) J) ^ e = (I ^ e).map (algebraMap k B) := by
    rw [Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq k Raw B, ← Ideal.map_pow]
  have hS : J ^ e = (I ^ e).map (algebraMap k Raw) := by rw [Ideal.map_pow]
  let equiv := ((Ideal.quotientEquivAlgOfEq Raw hC.symm).trans
    (adicCompletionPowQuotientEquiv J (hI.map _) e)).trans
    (Ideal.quotientEquivAlgOfEq Raw hS)
  change equiv (Ideal.Quotient.mk _ (algebraMap Raw B x)) = _
  simp only [equiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  have hm := adicCompletionPowQuotientEquiv_algebraMap J (hI.map (algebraMap k Raw)) e x
  rw [hm, Ideal.quotientEquivAlgOfEq_mk]

/-- 小さい分冪模型の完備化の有限冪商は、対応する係数の商上で平坦。 -/
theorem pdRawCompletionQuotient_flat (e : ℕ) :
    let B := AdicCompletion J Raw
    Module.Flat (k ⧸ (I ^ e)) (B ⧸ ((I ^ e).map (algebraMap k B))) := by
  let : Module.Free k Raw := Module.Free.of_basis (pdRawBasis k r n)
  exact adicCompletionBasePowQuotient_flat (S := Raw) I (Submodule.fg_span_singleton _) e

/-- p 正則な小さい分冪模型では、各項の主完備化は古典的な完備化で表される。 -/
def pdRawPrincipalCompletionIso (hreg : Function.Injective (fun x : k => (p : k) * x)) :
    letI := principalCompletionCommRing Raw (p : Raw)
    letI := principalCompletionAlgebra Raw (p : Raw)
    PrincipalCompletionH0 Raw (p : Raw) ≃ₐ[Raw] AdicCompletion (Ideal.span {(p : Raw)}) Raw :=
  principalCompletionAdicAlgEquiv Raw (p : Raw) (PDSmallRawEnvelope.raw_regular p r n hreg)

end SerrePositivity.BhattScholze.Prismatic
