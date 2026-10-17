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

/--
## 概要
perfectoid 化の核で割った R/K は perfectoid 環である。
## 方針
B4 の一般全射性と既存の核商同型により、B3 の選ばれた perfectoid 化に移す。
## 規約
単項商の導来完備性を使い、p ねじれなしを仮定しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の商の実積の標的の完備性を供給する。
-/
theorem perfectoidIdeal_quotient_isIntegralPerfectoid :
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
    (perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g)

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
  have hQ := perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g
  exact ⟨integralPerfectoid_completedDerivedIdealMul_isIso p _ hR hQ,
    integralPerfectoid_completedQuotientMul_isIso p R _ hR hQ,
    integralPerfectoid_completedIdealTensorQuotient_isZero p _ hR hQ⟩

/--
## 概要
商の実完備導来自己テンソルから、元の商 (R/K)[0] への標準積を定義する。
## 方針
元の導来積の完備化に、perfectoid 商の標準完備化単位の逆を合成する。
## 規約
K は perfectoidIdeal であり、標的の別コピーへの抽象的同型で代用しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の第二射を元の商を標的として渡す。
-/
def perfectoidIdeal_completedQuotientMul :
    let Q := R ⧸ perfectoidIdeal R p hR g
    (derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R Q)).obj (ModuleCat.of R Q)) ⟶
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R Q) :=
  (derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ perfectoidIdeal R p hR g)).hom ≫
    (derivedComplexCompletionUnitIso R (p : R) _
      ((perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g).isModuleComplete_algebra R _ p)).inv

/--
## 概要
元の商を標的とする実積 (R/K)⊗̂ᴸ(R/K)→(R/K)[0] は同型である。
## 方針
Lemma 10.3 の第二主張と、標的の perfectoid 性による標準単位同型を合成する。
## 規約
完備化単位によって定義した同じ積について主張する。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の元の商を標的とする第二主張である。
-/
theorem perfectoidIdeal_completedQuotientMul_isIso :
    IsIso (perfectoidIdeal_completedQuotientMul R p hR g) := by
  have := (perfectoidIdeal_lemma103 R p hR g).2.1
  unfold perfectoidIdeal_completedQuotientMul
  infer_instance

end SerrePositivity.BhattScholze
