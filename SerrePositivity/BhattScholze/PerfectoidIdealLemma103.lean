module

public import SerrePositivity.BhattScholze.Lemma103PerfectoidTensor
public import SerrePositivity.BhattScholze.Lemma103KernelTensor
public import SerrePositivity.BhattScholze.SemiperfectoidSurjectivity
public import SerrePositivity.BhattScholze.PerfectoidRingEquiv
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdeal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComplete

/-!
# 単項商の perfectoid 化の核に対する Lemma 10.3
## 概要
B3 の選ばれた perfectoid 化の核について、BS 著者版 Lemma 10.3（印刷 pp.78–79）を述べる。
## 方針
B4 の一般全射性により商を元の perfectoid 化へ同定し、一般 perfectoid 商の結果を適用する。
## 規約
既存の perfectoidIdeal と IsPerfectoidization を使い、p ねじれなしを仮定しない。
## 使われ方
Remark 10.7 の mod p 冪冪等性と Prop 10.2 の拡大閉性の入口である。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

private lemma quotientPerfectoid :
    IsIntegralPerfectoid (R ⧸ perfectoidIdeal R p hR g) p := by
  let f := toQuotientPerfectoidization R (Ideal.span {g}) p hR
  have hf := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  have hs : Function.Surjective f :=
    surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR
      (Ideal.Quotient.mk (Ideal.span {g})) Ideal.Quotient.mk_surjective
      (isModuleComplete_principal_quotient_natCast R p g (hR.isModuleComplete R p)) f hf
  let e : R ⧸ perfectoidIdeal R p hR g ≃+*
      QuotientPerfectoidization R (Ideal.span {g}) p hR :=
    RingHom.quotientKerEquivOfSurjective (hs.comp Ideal.Quotient.mk_surjective)
  exact isIntegralPerfectoid_of_ringEquiv p e.symm hf.1

/--
## 概要
単項商の perfectoid 化の核 K は導来 p 完備である。
## 方針
B4 の全射性による perfectoid 商表示に、一般の核の完備性を適用する。
## 規約
K は既存の perfectoidIdeal そのものである。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の第一射の標的を固定する。
-/
theorem perfectoidIdeal_isModuleComplete :
    IsModuleComplete R (p : R) (ModuleCat.of R (perfectoidIdeal R p hR g)) :=
  integralPerfectoid_quotientIdeal_isModuleComplete p (perfectoidIdeal R p hR g) hR
    (quotientPerfectoid R p hR g)

/--
## 概要
K を単項商の perfectoid 化の核とすると、実積 K⊗̂ᴸK→K と
(R/K)⊗̂ᴸ(R/K)→(R/K) の完備化は同型であり、K⊗̂ᴸ(R/K) は零である
（BS 著者版 Lemma 10.3、印刷 pp.78–79）。
## 方針
B4 による同じ核の perfectoid 商表示に、一般商の三角形による三主張を適用する。
## 規約
第一射は元の K[0] を標的とする標準積。第二射の標的の完備化は
perfectoid 商の導来完備性で元の商に標準同定される。p 正則性は追加しない。
## 使われ方
Remark 10.7 と Prop 10.2 の核イデアルに関する結果を供給する。
-/
theorem perfectoidIdeal_lemma103 :
    let K := perfectoidIdeal R p hR g
    IsIso (completedDerivedIdealMul (p : R) K
      (perfectoidIdeal_isModuleComplete R p hR g)) ∧
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ K)).hom) ∧
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R K)).obj
        (ModuleCat.of R (R ⧸ K)))) := by
  have hQ := quotientPerfectoid R p hR g
  exact ⟨integralPerfectoid_completedDerivedIdealMul_isIso p _ hR hQ,
    integralPerfectoid_completedQuotientMul_isIso p R _ hR hQ,
    integralPerfectoid_completedIdealTensorQuotient_isZero p _ hR hQ⟩

end SerrePositivity.BhattScholze
