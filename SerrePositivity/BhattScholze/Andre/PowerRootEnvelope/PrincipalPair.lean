module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.RegularSwap
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.PrincipalPairRegularity

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiPD
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# 正則対の主完備化

## 概要
三元正則性の関係追加による保存、正則対の主冪商と第一完備化、二座標完備化での各元の正則性、主完備化の第一剰余。
BS 著者版 Remark 7.15 の包の完備化に使う、正則な主元対の完備化を扱う。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPrism`、`PowerRootEnvelope/DeltaDivisionResidue`、`PowerRootEnvelope/Unconditional/RawRegular`。
-/

universe u v

/-! ## 三元正則性の関係追加による保存

## 概要

a が正則で、mod a の c と g、および mod(a,c) の g が正則なら、
g を課した後も a と mod a の c は正則。
BS 著者版 Remark 7.15（著者版 p.62）の有限 δ 関係商の同時帰納法に使う。

## 方針

正則対の順序交換を二度使い、二重主イデアル商の順序を交換する。

## 規約

任意の可換環を扱い、完備性・局所性・非零性を要求しない。

## 使われ方

a=p、c=d、g=次の δ 関係として有限段へ適用する。
-/

@[expose] public noncomputable section RegularTripleQuotientStep

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- 概要：環同型は p 正則性と mod p の指定係数の正則性を同時に移す。
方針：自然数保存で mod p 商同型を作り、通常の正則性の移送を使う。
規約：p は任意の自然数でよい。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の初期段と次有限段の照合。 -/
theorem ringEquiv_prime_pair_regular (e : R ≃+* S) (p : ℕ) (c : R)
    (hp : IsSMulRegular R (p : R))
    (hc : IsSMulRegular (R ⧸ Ideal.span {(p : R)})
      (Ideal.Quotient.mk (Ideal.span {(p : R)}) c)) :
    IsSMulRegular S (p : S) ∧ IsSMulRegular (S ⧸ Ideal.span {(p : S)})
      (Ideal.Quotient.mk (Ideal.span {(p : S)}) (e c)) := by
  refine ⟨?_, ?_⟩
  · have h := (ringEquiv_isSMulRegular e (p : R)).mp hp
    simpa only [map_natCast] using h
  · let ep : (R ⧸ Ideal.span {(p : R)}) ≃+* S ⧸ Ideal.span {(p : S)} :=
      Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
    have h := (ringEquiv_isSMulRegular ep _).mp hc
    change IsSMulRegular (S ⧸ Ideal.span {(p : S)})
      (Ideal.quotientEquiv _ _ e _ (Ideal.Quotient.mk _ c)) at h
    rw [Ideal.quotientEquiv_mk] at h
    exact h

/-- 概要：二つの主イデアルを順に課す順序を交換する環同型。
方針：一重二元商へ移し、生成元の順序を交換して戻す。
規約：代表元をそのまま保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の正則対の順序交換。 -/
def principalDoubleQuotSwapEquiv (a b : R) :
    ((R ⧸ Ideal.span {a}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) b}) ≃+*
      ((R ⧸ Ideal.span {b}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {b}) a}) :=
  ((principalDoubleQuotEquiv a b).trans (Ideal.quotEquivOfEq Ideal.span_pair_comm)).trans
    (principalDoubleQuotEquiv b a).symm

/-- 概要：二重主イデアル商の交換は元の代表元を保持する。
方針：一重二元商比較の代表元公式と逆合成を使う。
規約：全ての r∈R を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の商後の係数正則性。 -/
theorem principalDoubleQuotSwapEquiv_mk (a b r : R) :
    principalDoubleQuotSwapEquiv a b (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r) := by
  apply (principalDoubleQuotEquiv b a).injective
  simp only [principalDoubleQuotSwapEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, principalDoubleQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

/-- 概要：関係 g の追加後も a と mod a の c の正則性を保つ。
方針：a,g と mod a の c,g の二つの正則対を交換する。
規約：g は mod a と mod(a,c) の双方で正則とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限 δ 関係商の同時帰納法。 -/
theorem regularTripleQuotientStep (a c g : R)
    (ha : IsSMulRegular R a)
    (hc : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) c))
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g))
    (hgc : IsSMulRegular ((R ⧸ Ideal.span {a}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) c})
      (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {a}) c})
        (Ideal.Quotient.mk (Ideal.span {a}) g))) :
    IsSMulRegular (R ⧸ Ideal.span {g}) (Ideal.Quotient.mk (Ideal.span {g}) a) ∧
      IsSMulRegular ((R ⧸ Ideal.span {g}) ⧸
          Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a})
        (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a})
          (Ideal.Quotient.mk (Ideal.span {g}) c)) := by
  refine ⟨principal_regular_swap a g ha hg, ?_⟩
  have h := principal_regular_swap (Ideal.Quotient.mk (Ideal.span {a}) c)
    (Ideal.Quotient.mk (Ideal.span {a}) g) hc hgc
  let e := principalDoubleQuotSwapEquiv g a
  apply (ringEquiv_isSMulRegular e _).mpr
  rw [principalDoubleQuotSwapEquiv_mk]
  exact h

end SerrePositivity.BhattScholze.Andre

end RegularTripleQuotientStep

/-! ## 正則対の主冪商と第一完備化

## 概要

b が正則で c が mod b で正則なら、c は全ての mod bⁿ と b 完備化で正則。
BS 著者版 Remark 7.15（著者版 p.62）の正則対を完備化へ移すための一般環計算。

## 方針

c 倍が bⁿ で割り切れることから元の bⁿ 可除性を帰納し、完備化の各座標へ適用する。

## 規約

Noether 性・平坦性・b 完備性は要求しない。導来二座標完備化との比較は別工程。

## 使われ方

一元 raw 包の正則対から、その p 完備化における分母正則性を得る。
-/

