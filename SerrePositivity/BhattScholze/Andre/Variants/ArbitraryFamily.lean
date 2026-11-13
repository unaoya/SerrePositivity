module

public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary
public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicCandidate
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicSource
public import SerrePositivity.BhattScholze.Andre.Perfection.PerfectPrismMonic

/-!
# 任意のモニック族への一般化（主経路の有限族版の変種）

## 概要
`Envelope/MonicCandidate`・`Envelope/MonicSource`・`Perfection/PerfectPrismMonic` の主張を任意個のモニック族に広げたもの：残余導来評価比較、係数側剰余比較、源商上の導来還元、H⁰ の忠実平坦性、(p,d) 還元、逐次完備化後の剰余、冪零還元、G9 入力、完全 prism 上の源の離散性・raw PD 環・prism 候補・perfectoid 候補の完全忠実平坦性。
BS 著者版 Theorem 7.14 の根添加を、任意のモニック族に拡張するための材料をまとめる。

## 方針
主経路（`Transfinite`）は一元ずつ根を足すので有限族で足りる。任意族の結果として残す（BS-W8）。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Variants/MonicRootedExtension`、`Variants/RootedExtension`。
-/

universe u

/-! ## 任意モニック族の実残余導来評価比較

## 概要

任意モニック族の実残余自由 δ 源の導来評価は、実 raw (p,d) 剰余の single に同型。
BS 著者版 Remark 7.15（著者版 p.62）の実導来剰余比較。

## 方針

有界深さ有限部分族の余極限から得た全評価源の Tor 消滅を用いる。
標準導来 augmentation と通常残余テンソルの既存同型を合成する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる具体的 PD 計算の経路。

## 規約

添字型全体の有限性と多項式の正次数は不要。p 正則性と δ(d) の単元性を明示する。

## 使われ方

元の A/(p,d) 上の実還元と完備化に、有限性のない入力を供給する。
-/

@[expose] public noncomputable section MonicPrismaticArbitraryResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => (fun t : σ => monicRelation (f t) t)
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₁" => RingHom.comp (Ideal.Quotient.mk K₁)
  (deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d))
local notation "β₁" => deltaDivisionSourceEval E₁ c₁
local notation "Mψ" => baseChangeScalarModule ψ₁

local notation "Q₁" => L₁ ⧸ K₁
local notation "Res₁" => DeltaAdjoinDivisionResidue E₁ (MvPolynomial.C d) c₁

/-- 概要：任意モニック族の実残余終域の導来評価は raw (p,d) 商の次数零対象と標準同型。
方針：高次 Tor 消滅による標準 augmentation と、通常残余テンソルの既存同型を合成する。
規約：同じ元の自由 δ 源射と評価射を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数側の実導来剰余比較。 -/
def monicPrismaticArbitraryResidueSourceDerivedIso
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (boundedAboveDerivedBaseChange β₁).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₁ Res₁) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₁ c₁
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₁ (MvPolynomial.C d)
  letI : Module L₁ Q₁ := Algebra.toModule
  let e₁ : ((ModuleCat.extendScalars β₁).obj Mψ) ≃ₗ[P₁] (P₁ ⊗[L₁] Q₁) :=
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := e₁.trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₁ (MvPolynomial.C d) c₁).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₁ Mψ
    (monicPrismaticBoundedSupportResidueEval_torVanishing D d f hf hpA v hv) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticArbitraryResidue

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：モニック族の係数側の実導来剰余比較

## 概要

任意モニック族の f/d 包の自由 δ 源上の実三因子還元は、実 raw (p,d) 剰余の single に同型。
BS 著者版 Remark 7.15（著者版 p.62）の元の係数環への比較の準備。

## 方針

既存の一般結合子と右因子の商比較、前工程の標準導来評価比較を合成する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる実関係による計算。

## 規約

正次数は不要。元の係数作用を保つ具体的な導来同型を構成する。

## 使われ方

実自由 δ 源の商上へ作用を降下し、元の A/(p,d) 上でのホモロジーを計算する。
-/

@[expose] public noncomputable section ArbitraryMonicPrismaticCoefficientReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)


/-- 概要：任意モニック族について、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
def monicPrismaticSourceCoefficientResidueIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    MonicPrismaticSourceCoefficientReduced D d f ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ (MvPolynomial.C d) c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (monicPrismaticArbitraryResidueSourceDerivedIso D d f hf hpA v hv)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 概要：実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
def monicPrismaticSourceCoefficientResidueHomologyZeroIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (MonicPrismaticSourceCoefficientReduced D d f).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (monicPrismaticSourceCoefficientResidueIso_arbitrary D d f hf hpA v hv))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 概要：実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
theorem monicPrismaticSourceCoefficientResidue_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (MonicPrismaticSourceCoefficientReduced D d f).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientResidueIso_arbitrary D d f hf hpA v hv)))

end SerrePositivity.BhattScholze.Andre

end ArbitraryMonicPrismaticCoefficientReduction

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：モニック族の実自由 δ 源商上の導来還元

## 概要

任意モニック族の実導来還元は、作用を降下した raw (p,d) 剰余の single と同型。
BS 著者版 Remark 7.15（著者版 p.62）の実係数商への比較。

## 方針

自由 δ 源から商への全射性で H⁰ の線形比較を降下し、ホモロジー消滅と正規化純対象比較を使う。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる実関係による計算。

## 規約

モニック性、p 正則性、δ(d) の単元性を仮定する。正次数は不要。

## 使われ方

元の係数環の (p,d) 商へ制限して、実導来剰余の忠実平坦性へ接続する。
-/

@[expose] public noncomputable section ArbitraryMonicPrismaticQuotientDerived

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ (MvPolynomial.C d) c₀
local notation "r₀" => Ideal.Quotient.mk
  (deltaAdjoinDivisionResidueIdeal E₀ (MvPolynomial.C d) c₀)






/-- 概要：実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientDerivedRestrictedH0Iso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (MonicPrismaticSourceQuotientDerived D d f).obj) ≅ MRes :=
  ((derivedRestrictScalarsHomologyIso q₀ 0).app
      (MonicPrismaticSourceQuotientDerived D d f).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceQuotientDerivedRestrictionIso D d f)) ≪≫
    monicPrismaticSourceCoefficientResidueHomologyZeroIso_arbitrary
      D d f hf hpA v hv

/-- 概要：任意モニック族について、実商環上の還元そのものの非零次数ホモロジーが消える。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem monicPrismaticSourceQuotientDerived_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (MonicPrismaticSourceQuotientDerived D d f).obj) := by
  have hz := monicPrismaticSourceCoefficientResidue_homology_isZero_arbitrary
    D d f hf hpA v hv i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceQuotientDerivedRestrictionIso D d f)))
  have hr := (derivedRestrictScalarsHomologyIso q₀ i).app
    (MonicPrismaticSourceQuotientDerived D d f).obj
  have hs := hr.isZero_iff.mp hz'
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (MonicPrismaticSourceQuotientDerived D d f).obj) :=
    ModuleCat.subsingleton_of_isZero (R := L₀) hs
  exact ModuleCat.isZero_of_subsingleton _

/-- 概要：実商環上でのH0同型。qの全射性により、L線形比較を実Q線形比較へ昇格する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientDerivedH0Iso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (MonicPrismaticSourceQuotientDerived D d f).obj) ≅ ModuleCat.of Q₀ Res₀ := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := monicPrismaticSourceQuotientDerivedRestrictedH0Iso_arbitrary
    D d f hf hpA v hv ≪≫ (monicPrismaticSourceQuotientResidueRestrictionIso D d f).symm
  refine
    { hom := { hom' :=
        { toFun := e.hom.hom
          map_add' := e.hom.hom.map_add
          map_smul' := ?_ } }
      inv := { hom' :=
        { toFun := e.inv.hom
          map_add' := e.inv.hom.map_add
          map_smul' := ?_ } }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.hom.hom.map_smul r x
    change e.hom.hom ((q₀ r) • x) = (q₀ r) • e.hom.hom x at h
    exact h
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.inv.hom.map_smul r x
    change e.inv.hom ((q₀ r) • x) = (q₀ r) • e.inv.hom x at h
    exact h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.hom_inv_id
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.inv_hom_id

local notation "X₀" => MonicPrismaticSourceQuotientDerived D d f

/-- 概要：任意モニック族の実商還元は、標準t構造の非負部分に属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem monicPrismaticSourceQuotientDerived_isGE_zero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact monicPrismaticSourceQuotientDerived_homology_isZero_arbitrary
    D d f hf hpA v hv i (by omega)

/-- 概要：同じ入力の下で標準t構造の非正部分にも属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem monicPrismaticSourceQuotientDerived_isLE_zero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact monicPrismaticSourceQuotientDerived_homology_isZero_arbitrary
    D d f hf hpA v hv i (by omega)

/-- 概要：実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientDerivedSingleIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := monicPrismaticSourceQuotientDerived_isGE_zero_arbitrary D d f hf hpA v hv
  have := monicPrismaticSourceQuotientDerived_isLE_zero_arbitrary D d f hf hpA v hv
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (X₀).obj 0) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (monicPrismaticSourceQuotientDerivedH0Iso_arbitrary D d f hf hpA v hv)


end SerrePositivity.BhattScholze.Andre

end ArbitraryMonicPrismaticQuotientDerived

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：実商還元の H⁰ の元の係数商上の忠実平坦性

## 概要

任意正次数モニック族の実自由 δ 源商上の導来還元の H⁰ は、元の A/(p,d) 上忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の係数作用を保つ剰余比較。

## 方針

H⁰ の実源商線形比較を係数商へ制限し、明示した raw 剰余の標準係数作用と一致させる。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の計算。

## 規約

一般 (p,d) 商に沿う実還元を使う。Koszul 還元との無条件な同一視はしない。

## 使われ方

元の係数環上の実導来還元の平坦性と、完備化後の離散性の入力。
-/

@[expose] public noncomputable section ArbitraryMonicPrismaticQuotientFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "k₀" => Ideal.span {(p : A), d}
local notation "κ₀" => Ideal.Quotient.mk k₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ (MvPolynomial.C d) c₀
local notation "r₀" => Ideal.Quotient.mk
  (deltaAdjoinDivisionResidueIdeal E₀ (MvPolynomial.C d) c₀)

set_option maxHeartbeats 800000 in
-- 実商環上のホモロジーと複数の商作用を同時に照合するため。
/-- 概要：任意モニック族について、実導来商還元のH0は元のA/(p,d)上忠実平坦。
方針：実源商上の H⁰ 同型を元の係数商へ制限し、係数の代表元公式で忠実平坦性を移す。
規約：モニック性、正次数、p 正則性、δ(d) の単元性を要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上の実導来剰余入力。 -/
theorem monicPrismaticSourceQuotientDerivedH0_faithfullyFlat_arbitrary
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat (A ⧸ k₀)
      ((ModuleCat.restrictScalars (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (MonicPrismaticSourceQuotientDerived D d f).obj)) := by
  have hg := deltaRootSource_ghostMap_injective (σ := σ) hpA
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  let := monicPrismaticRawResidueBaseAlgebra D d f hpA hg v hv
  let H := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
    (MonicPrismaticSourceQuotientDerived D d f).obj
  let M := (ModuleCat.restrictScalars
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj H
  let eQ := monicPrismaticSourceQuotientDerivedH0Iso_arbitrary D d f hf hpA v hv
  let e : M ≃ₗ[A ⧸ k₀] Res₀ :=
    { toFun := eQ.hom.hom
      invFun := eQ.inv.hom
      left_inv := fun x => congrArg (fun f => f.hom x) eQ.hom_inv_id
      right_inv := fun x => congrArg (fun f => f.hom x) eQ.inv_hom_id
      map_add' := eQ.hom.hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        change H at x
        have h := eQ.hom.hom.map_smul
          (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) x
        change eQ.hom.hom ((deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          monicPrismaticSourceQuotientResidueMap D d f
            (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) * eQ.hom.hom x at h
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          monicPrismaticSourceQuotientResidueMap_mk, deltaDivisionSourceEval_C] at h
        change eQ.hom.hom ((deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          monicPrismaticRawResidueBaseMap D d f hpA hg v hv (κ₀ a) * eQ.hom.hom x
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          monicPrismaticRawResidueBaseMap_mk]
        exact h }
  have := monicPrismaticRawResidue_faithfullyFlat D d f hpA hg v hv hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e


end SerrePositivity.BhattScholze.Andre

end ArbitraryMonicPrismaticQuotientFlat

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：元の係数環上の実 (p,d) 還元と raw 残余商

## 概要

任意正次数モニック族の f/d 源の実 (p,d) 還元は離散的で、H⁰ が元の A/(p,d) 上忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の元の係数作用を保つ剰余計算。

## 方針

二重多項式係数包含の一般導来正方形比較を再利用し、実源商上で得た同型と忠実平坦性を移す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

離散性には正次数は不要。完備化後の離散性は別工程。

## 使われ方

実逐次 p,d 完備化と、その生成元冪商への還元の入力。
-/

@[expose] public noncomputable section ArbitraryMonicPrismaticPDReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "LCoef" => algebraMap A L₀
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)



local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀))
  (MonicPrismaticSourceCoefficientObject D d f)

/-- 概要：元のA上の実モニック族添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def monicPrismaticSourceCoefficientPDResidueIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact monicPrismaticSourceCoefficientPDReductionIso D d f ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (monicPrismaticSourceQuotientDerivedSingleIso_arbitrary D d f hf hpA v hv) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 概要：元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def monicPrismaticSourceCoefficientPDResidueH0Iso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 概要：元のA上の実(p,d)還元の非零次数ホモロジーは零。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem monicPrismaticSourceCoefficientPDResidue_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv)))

/-- 概要：元のA上の実(p,d)還元のH0は、実係数商A/(p,d)上忠実平坦。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem monicPrismaticSourceCoefficientPDResidueH0_faithfullyFlat_arbitrary
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars κ₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (MonicPrismaticSourceQuotientDerived D d f).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceCoefficientPDReductionIso D d f)) ≪≫
    (derivedRestrictScalarsHomologyIso κ₀ 0).app (MonicPrismaticSourceQuotientDerived D d f).obj
  have := monicPrismaticSourceQuotientDerivedH0_faithfullyFlat_arbitrary
    D d f hf hdeg hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end ArbitraryMonicPrismaticPDReduction

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：実逐次 p,d 完備化後のモニック源の剰余

## 概要

任意正次数モニック族の f/d 源を p,d の順に実導来完備化した対象の実 (p,d) 還元は
離散的で、H⁰ は元の A/(p,d) 上忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の準備。

## 方針

p と d の個別の正則性により一般の逐次完備化単位比較を用い、元の実剰余計算へ戻す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

d mod p の正則性は仮定しない。実完備化対象自体の離散性はまだ主張しない。

## 使われ方

冪零厚化と生成元冪商上の導来完備 Nakayama 判定へ渡す。
-/

@[expose] public noncomputable section ArbitraryMonicPrismaticIteratedResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => MonicPrismaticSourceCoefficientObject D d f
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)




/-- 概要：任意モニック族について、逐次主元完備化後の実還元は標準作用付きraw残余商のsingle対象。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
def monicPrismaticSourceIteratedPDResidueIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (MonicPrismaticSourceIteratedPDCompletion D d f) ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact monicPrismaticSourceIteratedPDReductionIso D d f hpA hd ≪≫
    monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv

/-- 概要：raw比較は合成標準単位の実還元を、未完備対象のraw比較へ送る。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidueIso_unit_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (monicPrismaticSourceIteratedPDResidueIso_arbitrary D d f hf hpA hd v hv).hom =
      (monicPrismaticSourceCoefficientPDResidueIso_arbitrary D d f hf hpA v hv).hom := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  simp only [monicPrismaticSourceIteratedPDResidueIso_arbitrary, Iso.trans_hom]
  rw [← Category.assoc, monicPrismaticSourceIteratedPDReductionIso_unit, Category.id_comp]

/-- 概要：逐次主元完備化後の実(p,d)還元の非零次数ホモロジーは零。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidue_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj) :=
  (monicPrismaticSourceCoefficientPDResidue_homology_isZero_arbitrary
    D d f hf hpA v hv i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (monicPrismaticSourceIteratedPDReductionIso D d f hpA hd)))

/-- 概要：逐次主元完備化後の実(p,d)還元のH0は、標準A/(p,d)上で忠実平坦。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、任意モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat_arbitrary
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀ ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceIteratedPDReductionIso D d f hpA hd))
  have := monicPrismaticSourceCoefficientPDResidueH0_faithfullyFlat_arbitrary
    D d f hf hdeg hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end ArbitraryMonicPrismaticIteratedResidue

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：モニック源の生成元冪商の標準冪零還元

## 概要

実逐次 p,d 完備化の A/(p,dⁿ) 還元を標準冪零商でさらに還元すると、
raw 剰余の係数作用を保つ single になる。BS 著者版 Remark 7.15（著者版 p.62）の冪商計算。

## 方針

一般の冪零商・合成係数拡大の比較と、前工程の実 (p,d) 還元比較を合成する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

n は正とする。二つの元の個別の正則性を使い、正則列とは仮定しない。

## 使われ方

冪零還元からの純性・平坦性の既存判定 G10 へ、同じ実対象の入力を渡す。
-/

@[expose] public noncomputable section ArbitraryMonicPrismaticCanonicalPowerResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) (n : ℕ) (hn : 0 < n)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "qₙ" =>
  Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))
local notation "rₙ" => prismaticPowerResidueMap (p : A) d n hn
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange rₙ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀)

local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Sₙ" => Tₙ ⧸ Kₙ
local notation "eₙ" => prismaticPowerResidueQuotientEquiv (p : A) d n hn
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀
local notation "W₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀
local notation "MCan" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars (RingEquiv.toRingHom eₙ)) MRes

/-- 概要：G10の標準冪零商による実還元は、商環上の標準raw加群のsingle対象。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：任意モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
def monicPrismaticSourceCanonicalPowerResidueIso_arbitrary (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    W₀ ≅ boundedAboveDerivedSingleFunctor.obj MCan := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      ((prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm ≪≫
        monicPrismaticSourceIteratedPDResidueIso_arbitrary D d f hf hpA hd v hv) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso (eₙ).toRingHom 0).app MRes)

include hn in
/-- 概要：標準冪零商による実還元の非零次数ホモロジーは零。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：任意モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
theorem monicPrismaticSourceCanonicalPowerResidue_homology_isZero_arbitrary
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MCan i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCanonicalPowerResidueIso_arbitrary
          D d f n hn hf hpA hd v hv)))

include hn in
/-- 概要：標準冪零商による実還元のH0は、その正確な商環上で忠実平坦。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：任意モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
theorem monicPrismaticSourceCanonicalPowerResidueH0_faithfullyFlat_arbitrary
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj
  let eH : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj M :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀)) ≪≫
      (derivedRestrictScalarsHomologyIso (eₙ).toRingHom 0).app (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Sₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Sₙ R₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Sₙ ≃ₐ[Sₙ] R₀ :=
    AlgEquiv.ofBijective (Algebra.ofId Sₙ R₀) (eₙ).bijective
  have : Module.FaithfullyFlat Sₙ R₀ :=
    Module.FaithfullyFlat.of_linearEquiv Sₙ Sₙ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat R₀ M := by
    let N := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X₀).obj
    let eM : M ≅ N := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm)
    have : Module.FaithfullyFlat R₀ N :=
      monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat_arbitrary D d f hf hdeg hpA hd v hv
    exact Module.FaithfullyFlat.of_linearEquiv R₀ N eM.toLinearEquiv
  have : Module.FaithfullyFlat Sₙ M := Module.FaithfullyFlat.trans Sₙ R₀ M
  exact Module.FaithfullyFlat.of_linearEquiv Sₙ M eH.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end ArbitraryMonicPrismaticCanonicalPowerResidue

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：モニック源の実生成元冪商の G9 入力

## 概要

任意正次数モニック族の実逐次完備化の A/(p,dⁿ) 還元は離散かつ H⁰ が平坦であり、
A/(dⁿ) 還元は p 導来完備で標準 mod p 還元が離散かつ平坦。
BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商計算。

## 方針

同じ実対象の標準冪零還元に G10 を適用し、一般商比較と G8 の完備性を接続する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

正の冪と元の係数射に沿う実還元を使い、d mod p の正則性は要求しない。

## 使われ方

生成元冪商に G9 を適用し、完備化源の離散性と平坦性を導く。
-/

@[expose] public noncomputable section ArbitraryMonicPrismaticSourcePowerInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) (n : ℕ) (hn : 0 < n)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
  (hd : IsSMulRegular A d) (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X₀
local notation "Tₙ" => A ⧸ Ideal.span {d ^ n}
local notation "Mₙ" => Tₙ ⧸ Ideal.span {(p : Tₙ)}
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))) X₀
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : Tₙ)}))) Zₙ
include hn hf hdeg  hpA hd v hv

/-- 概要：G10により、実A/(p,dⁿ)還元は次数零に集中しH0が平坦。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、任意正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidue_pure_flat_arbitrary :
    (Y₀).obj.IsGE 0 ∧ (Y₀).obj.IsLE 0 ∧
      Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) := by
  have hPure := monicPrismaticSourceCanonicalPowerResidue_homology_isZero_arbitrary
    D d f n hn hf hpA hd v hv
  have hFF := monicPrismaticSourceCanonicalPowerResidueH0_faithfullyFlat_arbitrary
    D d f n hn hf hdeg hpA hd v hv
  let := hFF
  exact derived_pure_flat_of_nilpotent_reduction Kₙ Y₀ hPure
    inferInstance ⟨n, prismaticPowerResidueIdeal_pow (p : A) d n⟩

/-- 概要：G10で得た実冪剰余の非零次数ホモロジー消滅。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、任意正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidue_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Y₀).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    monicPrismaticSourcePowerResidue_pure_flat_arbitrary D d f n hn hf hdeg hpA hd v hv
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 概要：同じ実冪剰余のH0平坦性。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、任意正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidueH0_flat_arbitrary :
    Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) :=
  (monicPrismaticSourcePowerResidue_pure_flat_arbitrary D d f n hn hf hdeg hpA hd v hv).2.2

/-- 概要：A/(dⁿ)上の標準mod p実還元の非零次数ホモロジー消滅。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、任意正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPowerModP_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModP_homology_isZero p d n X₀ i
    (monicPrismaticSourcePowerResidue_homology_isZero_arbitrary D d f n hn hf hdeg hpA hd v hv i hi)

/-- 概要：標準mod p実還元のH0は、その正確な商環上で平坦。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、任意正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPowerModPH0_flat_arbitrary :
    Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModPH0_flat p d n X₀
    (monicPrismaticSourcePowerResidueH0_flat_arbitrary D d f n hn hf hdeg hpA hd v hv)

/-- 概要：G8の商上完備性とG10の実mod p入力を、G9用の同じ対象で束ねる。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、任意正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPower_G9_inputs_arbitrary :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  exact ⟨monicPrismaticSourceGeneratorPowerReduction_isComplete_over_quotient D d f hd n,
    monicPrismaticSourceGeneratorPowerModP_homology_isZero_arbitrary D d f n hn hf hdeg hpA hd v hv,
    monicPrismaticSourceGeneratorPowerModPH0_flat_arbitrary D d f n hn hf hdeg hpA hd v hv⟩

end SerrePositivity.BhattScholze.Andre

end ArbitraryMonicPrismaticSourcePowerInputs

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：完全 prism 上の任意モニック族の実完備化源の離散性

## 概要

完全 prism 上の任意正次数モニック族の一般 f/d 源を p,d の順に実導来完備化すると離散的となる。
BS 著者版 Remark 7.15（著者版 p.62）の実 prismatic envelope 比較への入力。

## 方針

完全 prism の生成元冪商の p 冪ねじれ上界と、標準 mod p 還元の離散・平坦性から G9 を適用する。
その生成元商の離散性と d 導来完備性から元の対象の純性を得る。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の計算。

## 規約

正次数モニック性を要求する。最終 perfectoid 商との環同型は別工程。

## 使われ方

同じ実 H⁰ を raw PD 完備化環へ比較して、元の係数射の完全忠実平坦性を導く。
-/

@[expose] public noncomputable section ArbitraryPerfectPrismMonicSourceDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "X" => MonicPrismaticSourceIteratedPDCompletion D d f
include hP hf hdeg

/-- 概要：完全 prism 上の任意モニック族の実完備化源の正の生成元冪商は離散的。
方針：標準 mod p の離散・平坦性、p 導来完備性、生成元冪商の p 冪ねじれ上界を G9 へ渡す。
規約：d mod p の正則性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の実完備化対象の離散性。 -/
theorem perfectPrismMonicSourcePower_pure_arbitrary (n : ℕ) (hn : 0 < n) :
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 := by
  let T := A ⧸ Ideal.span {d ^ n}
  let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  obtain ⟨hc, hz, hflat⟩ := monicPrismaticSourceGeneratorPower_G9_inputs_arbitrary D d f n hn
    hf hdeg hP.p_mul_injective P.generator_regular v hv
  have hbound : ∃ N : ℕ, ∀ k : ℕ, ∀ x : T,
      (p : T) ^ k * x = 0 → (p : T) ^ N * x = 0 := by
    let := P.isAdicComplete_p_of_perfect hP
    exact ⟨n, fun k x hx => hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
      (P.isDistinguished_generator) n k x hx⟩
  exact derived_pure_of_complete_flat_reduction (p : T) Z hz hflat hbound hc

/-- 概要：完全 prism 上の任意モニック族の実逐次 p,d 完備化源は離散的。
方針：生成元商の離散性、生成元の正則性、d 導来完備性を一般純性判定へ渡す。
規約：同じ元の係数環上の実対象を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ を環候補へ比較する。 -/
theorem perfectPrismMonicSource_pure_arbitrary : (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := by
  have hmod (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj) := by
    have hpow := perfectPrismMonicSourcePower_pure_arbitrary P hP f hf hdeg 1 (by omega)
    dsimp only at hpow
    rw [pow_one] at hpow
    rcases lt_or_gt_of_ne hi with h | h
    · exact (DerivedCategory.isGE_iff _ _).mp hpow.1 i h
    · exact (DerivedCategory.isLE_iff _ _).mp hpow.2 i h
  obtain ⟨hGE, hLE, _⟩ := derived_pure_of_complete_regular_quotient_pure d
    P.generator_regular X (monicPrismaticSourceIteratedPDCompletion_isComplete_d D d f) hmod
  exact ⟨hGE, hLE⟩

/-- 概要：同じ実逐次完備化源の全非零次数ホモロジーは零。
方針：純性を標準 t 構造のホモロジー消滅として展開する。
規約：全非零整数次数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数射の実還元計算への接続。 -/
theorem perfectPrismMonicSource_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismMonicSource_pure_arbitrary P hP f hf hdeg
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 概要：実完備化源は同じ実 H⁰ の single と正規化された同型を持つ。
方針：標準 t 構造の純対象の既存正規化比較を使う。
規約：元の A 作用と実 H⁰ を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較へ渡す。 -/
def perfectPrismMonicSourceSingleIso_arbitrary :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismMonicSource_pure_arbitrary P hP f hf hdeg
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (X).obj 0

end SerrePositivity.BhattScholze.Andre

end ArbitraryPerfectPrismMonicSourceDiscrete

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：任意モニック族の raw 実 PD 環の完全忠実平坦性

## 概要

完全 prism 上の任意正次数モニック族の raw f/d 包の実 PD 完備化環は、元の (p,d) に関して
完全忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の環候補への平坦性の移送。

## 方針

同じ実源の離散性と、元の係数作用を保つ H⁰ 比較から raw PD 環の single 比較を構成する。
実剰余の Tor 消滅と忠実平坦性を完全忠実平坦性の一般判定へ渡す。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の計算。

## 規約

この raw PD 環の完全 δ 化と最終 perfectoid 商への比較は別工程。

## 使われ方

完全 δ 化と実完備化の既存比較を介して、最終根付き perfectoid 候補の平坦性へ進む。
-/

@[expose] public noncomputable section ArbitraryPerfectPrismMonicRawPDCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "B" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (boundedAboveDerivedSingleFunctor.obj M)
include hP hf hdeg

/-- 概要：元の実逐次源は、標準A作用付きraw PD環のsingle対象と同型。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
def perfectPrismMonicSourcePDSingleIso_arbitrary : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
  ObjectProperty.isoMk _ (perfectPrismMonicSourceSingleIso_arbitrary P hP f hf hdeg ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso (monicPrismaticSourcePDH0Iso D d f))

/-- 概要：実PD環の同じ(p,d)導来還元の非零次数は消える。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_reduction_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  have hz := monicPrismaticSourceIteratedPDResidue_homology_isZero_arbitrary D d f hf
    hP.p_mul_injective P.generator_regular v hv i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange q).mapIso
        (perfectPrismMonicSourcePDSingleIso_arbitrary P hP f hf hdeg)))).symm

/-- 概要：実PD環の同じ(p,d)導来還元のH0は忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_reductionH0_faithfullyFlat_arbitrary :
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat_arbitrary D d f hf hdeg
    hP.p_mul_injective P.generator_regular v hv
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange q).mapIso
          (perfectPrismMonicSourcePDSingleIso_arbitrary P hP f hf hdeg)))).toLinearEquiv.symm

/-- 概要：実PD環の具体的A係数加群の(p,d)高次Torは零。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_torVanishing_arbitrary : scalarExtensionTorVanishing q M := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (perfectPrismMonicRawPD_reduction_homology_isZero_arbitrary P hP f hf hdeg (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 概要：実PD環の通常係数拡大も同じ商環上忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_scalarExtension_faithfullyFlat_arbitrary :
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    perfectPrismMonicRawPD_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 概要：任意正次数モニック族のraw実PD環は、元の(p,d)に関して完全忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_isCompletelyFaithfullyFlat_arbitrary :
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let Mc : ModuleCat.{u} A := M
  have hFF : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismMonicRawPD_scalarExtension_faithfullyFlat_arbitrary P hP f hf hdeg
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismMonicRawPD_torVanishing_arbitrary P hP f hf hdeg) hFF.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hFF
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze.Andre

end ArbitraryPerfectPrismMonicRawPDCompletelyFlat

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：raw モニック PD 環の δ 完全化への平坦性入力

## 概要

完全 prism 上の任意正次数モニック族の raw PD 環の標準係数射は δ 射で、
その δ 完全化の実 PD 完備化は元の (p,d) に関して完全忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への準備。

## 方針

raw PD 環の元の係数制限作用を標準環射の作用に同定し、既存の一般 δ 代数の定理を適用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる具体的な係数射の計算。

## 規約

完全化の対象は明示的に固定する。最終 f/d 候補との環比較と perfectoid 商は別工程。

## 使われ方

一般の完備化・δ 完全化の比較同型を介して、最終根付き候補へ完全忠実平坦性を移す。
-/

@[expose] public noncomputable section ArbitraryPerfectPrismMonicPDPerfectionInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

section Perfect
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

include hP hf hdeg

/-- 概要：完全prism上では、同じPD係数射に沿う実還元の非零次数は消える。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing Raw p z
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  have hz := perfectPrismMonicRawPD_reduction_homology_isZero_arbitrary P hP f hf hdeg  i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso (monicPrismaticPDSourceModuleIso D d f))))).symm

/-- 概要：同じ標準PD係数射に沿う実還元のH0は忠実平坦。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary :
    letI := pdCompletionCommRing Raw p z
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  let : Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj) :=
    perfectPrismMonicRawPD_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso
          (monicPrismaticPDSourceModuleIso D d f))))).toLinearEquiv.symm

/-- 概要：任意正次数モニック族の実PD環のδ完全化を逐次実完備化した具体的対象は離散。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDPerfectionCompletion_pure_arbitrary :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletion_pure P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg )

/-- 概要：同じ具体的δ完全化逐次対象の生成元冪商も離散でH0のp冪ねじれは有界。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には任意正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDPerfectionPower_pure_bounded_torsion_arbitrary (n : ℕ) (hn : 0 < n) :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    let T := A ⧸ Ideal.span {d ^ n}
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj Z.obj,
          (p : T) ^ k • x = 0 → (p : T) ^ N • x = 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg ) n hn

local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ

/-- 概要：任意正次数モニック族の raw PD 環を δ 完全化し再び実 PD 完備化した環は完全忠実平坦。
方針：元の標準係数射の実剰余の離散・忠実平坦性を、既存の一般 δ 代数の完全忠実平坦性へ渡す。
規約：元の (p,d) 係数作用を明示する。最終候補への環比較は別工程。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完成した完全 δ 環候補への平坦性の移送。 -/
theorem perfectPrismMonicPDPerfection_isCompletelyFaithfullyFlat_arbitrary :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p (κ d)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule t)) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  exact perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg )

end Perfect
end SerrePositivity.BhattScholze.Andre

end ArbitraryPerfectPrismMonicPDPerfectionInputs

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：任意モニック族の既存 prism 候補の完全忠実平坦性

## 概要

完全 prism 上の任意正次数モニック族の既存多項式 prism 候補は、標準係数射に関して
元の (p,d) 上完全忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の具体的候補への平坦性。

## 方針

PD 先行 δ 完全化で得た平坦性を、元の係数射を保つ具体的環・加群同型で既存候補へ移す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

標準係数射の toAlgebra を明示する。perfectoid 商上の p 完全忠実平坦性は別工程。

## 使われ方

既存の根方程式と整 perfectoid 性を持つ商候補へ p 完全忠実平坦性を移す。
-/

@[expose] public noncomputable section ArbitraryPerfectPrismMonicPrismCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp v c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "I" => Ideal.span {(p : A), d}
include hP hf hdeg

/-- 概要：任意正次数モニック族の既存多項式 prism 候補は、標準係数射の作用で完全忠実平坦。
方針：PD 先行完全化の平坦性を係数射を保つ加群同型で移し、toAlgebra の作用と照合する。
規約：元の (p,d) と同じ係数射を使う。有限全列挙以外の補助仮定を残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終 perfectoid 商の平坦性への入力。 -/
theorem perfectPrismMonicPrism_isCompletelyFaithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    letI := (φ).toAlgebra
    IsCompletelyFaithfullyFlat I T := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  have hM : IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule φ)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv I
      (monicPrismaticPDPerfectionCandidateModuleIso D d f).toLinearEquiv
      (perfectPrismMonicPDPerfection_isCompletelyFaithfullyFlat_arbitrary P hP f hf hdeg )
  let := (φ).toAlgebra
  let e : baseChangeScalarModule φ ≃ₗ[A] T :=
    { toFun := fun y => y
      invFun := fun y => y
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a y
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I e hM

end SerrePositivity.BhattScholze.Andre

end ArbitraryPerfectPrismMonicPrismCompletelyFlat

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：既存モニック prism 候補の標準剰余入力

## 概要

完全 prism 上の任意正次数モニック族について、既存候補の標準 (p,d) 係数拡大は高次 Tor が零で、
通常係数拡大が忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商への入力。

## 方針

一般 δ 代数の実 PD 完備化の同じ標準射の結果を、候補比較の A 線形同型で移す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる具体的係数射の計算。

## 規約

元の A 作用を持つ baseChangeScalarModule を固定し、商の基底環を取り替えない。

## 使われ方

生成元商と標準 mod p 商の実導来合成比較へ渡す。
-/

@[expose] public noncomputable section ArbitraryPerfectPrismMonicPrismResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun a : σ => monicRelation (f a) a)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp v c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "M" => baseChangeScalarModule φ
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
include hP hf hdeg

/-- 概要：既存候補の標準係数加群は元の (p,d) 商への拡大で高次 Tor が零。
方針：PD 先行構成の標準 Tor 消滅を係数射を保つ加群同型で移す。
規約：任意正次数モニック族と完全 prism を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商の実 mod p 還元。 -/
theorem perfectPrismMonicPrism_torVanishing_arbitrary :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing q M := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  exact scalarExtensionTorVanishing_of_iso q (monicPrismaticPDPerfectionCandidateModuleIso D d f)
    (perfectPrismDeltaAlgebraPD_torVanishing P G j hP
      (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
      (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
      (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg ))

/-- 概要：既存候補の同じ標準係数加群の通常 (p,d) 係数拡大は忠実平坦。
方針：PD 先行構成の通常剰余忠実平坦性を同じ線形比較で移す。
規約：元の係数商 A/(p,d) と実係数射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商上の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_scalarExtension_faithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  let M₀ : ModuleCat.{u} A := baseChangeScalarModule t
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M₀) :=
    perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat P G j hP
      (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
      (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
      (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg )
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q).obj M₀)
    (((ModuleCat.extendScalars q).mapIso
      (monicPrismaticPDPerfectionCandidateModuleIso D d f)).toLinearEquiv.symm)

end SerrePositivity.BhattScholze.Andre

end ArbitraryPerfectPrismMonicPrismResidue

/-! ## BS 著者版 Remark 7.15 の包の計算（任意族）：任意モニック族の標準 perfectoid 候補の p 完全忠実平坦性

## 概要

完全 prism 上の任意正次数モニック族の既存 perfectoid 候補の標準 A/d 基底射は p 完全忠実平坦。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の有限根付き候補。

## 方針

生成元商の実還元を標準候補の single と同定し、prism 側の (p,d) 剰余の Tor 消滅と
忠実平坦性を正確な標準 mod p 商へ移す。原典の BS 著者版 Proposition 7.11 を使う経路とは異なる計算。

## 規約

モニック性と正次数、有限全列挙を明示する。任意族への最終接続は別工程。

## 使われ方

既存の根方程式と整 perfectoid 性を合わせ、任意モニック族の根付き拡大を公開する。
-/

@[expose] public noncomputable section ArbitraryPerfectPrismMonicPerfectoidCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_generator P
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "M" => baseChangeScalarModule φ
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q₀" => Ideal.Quotient.mk I
local notation "g" => polynomialPerfectoidCandidateBaseMap D d f hd
local notation "N" => baseChangeScalarModule g
local notation "K" => Ideal.span {(p : R)}
local notation "Qp" => R ⧸ K
local notation "qp" => Ideal.Quotient.mk K
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qp)
  (Functor.obj boundedAboveDerivedSingleFunctor N)
include hP hf hdeg

/-- 概要：既存多項式 prismの同じ(p,d)実還元の非零次数は消える。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の任意正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_pair_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    letI := polynomialPrismCommRing D d f
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := polynomialPrismCommRing D d f
  let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q₀ M
    (perfectPrismMonicPrism_torVanishing_arbitrary P hP f hf hdeg )
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q₀).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

/-- 概要：同じ多項式 prismの実(p,d)還元のH0は忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の任意正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_pairH0_faithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := polynomialPrismCommRing D d f
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q₀).obj M) :=
    perfectPrismMonicPrism_scalarExtension_faithfullyFlat_arbitrary P hP f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q₀).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q₀).app M).toLinearEquiv

/-- 概要：perfectoid商の標準基底射の実mod p還元の非零次数は消える。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の任意正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_modP_homology_isZero_arbitrary (i : ℤ) (hi : i ≠ 0) :
    letI := polynomialPrismCommRing D d f
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj (Y).obj) := by
  let := polynomialPrismCommRing D d f
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj
      ((boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)).obj) := by
    let HQ (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismMonicPrism_pair_homology_isZero_arbitrary P hP f hf hdeg  i hi
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModP_homology_isZero p d 1 X i hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
      (perfectPrismMonicPrism_derivedQuotientIso P hP f)))).symm

/-- 概要：同じ実mod p還元のH0は、正確な基底剰余環上で忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の任意正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_modPH0_faithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Qp ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) := by
  let := polynomialPrismCommRing D d f
  let W := (boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj) := by
    let HQ (a : A) := Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), a})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismMonicPrism_pairH0_faithfullyFlat_arbitrary P hP f hf hdeg
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := Module.FaithfullyFlat
      ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModPH0_faithfullyFlat p d 1 X hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
        (perfectPrismMonicPrism_derivedQuotientIso P hP f)))).toLinearEquiv.symm

/-- 概要：同じperfectoid商の基底係数加群の高次mod p Torは零。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の任意正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_torVanishing_arbitrary :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing qp N := by
  let := polynomialPrismCommRing D d f
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff qp N).mp
  intro n hn
  exact (perfectPrismMonicPerfectoid_modP_homology_isZero_arbitrary
    P hP f hf hdeg  (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso qp).app N)).symm

/-- 概要：同じperfectoid商の通常mod p係数拡大は忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の任意正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_scalarExtension_faithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj N) := by
  let := polynomialPrismCommRing D d f
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) :=
    perfectPrismMonicPerfectoid_modPH0_faithfullyFlat_arbitrary P hP f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso qp).app N).toLinearEquiv.symm

/-- 概要：任意正次数モニック族のperfectoid候補の標準基底射はp完全忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の任意正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_isCompletelyFaithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    IsCompletelyFaithfullyFlat K (ModuleCat.carrier N) := by
  let := polynomialPrismCommRing D d f
  let Nc : ModuleCat.{u} R := N
  have hff : Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj Nc) :=
    perfectPrismMonicPerfectoid_scalarExtension_faithfullyFlat_arbitrary P hP f hf hdeg
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction K Nc
    (perfectPrismMonicPerfectoid_torVanishing_arbitrary P hP f hf hdeg ) hff.1, ?_⟩
  let e := (quotientScalarExtensionEquiv K Nc).trans (quotientTensorReductionEquiv K Nc).symm
  let := hff
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

/-- 概要：任意正次数モニック族の既存 perfectoid 候補の標準基底射は p 完全忠実平坦。
方針：制限加群の完全忠実平坦性を、同じ環射の toAlgebra の作用と恒等線形同型で照合する。
規約：基底環は元の A/d、係数射は候補構成の標準射を使う。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の有限根付き拡大。 -/
theorem perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    letI := (g).toAlgebra
    IsCompletelyFaithfullyFlat K (PolynomialPerfectoidCandidate D d f hd) := by
  let := polynomialPrismCommRing D d f
  have hN := perfectPrismMonicPerfectoid_isCompletelyFaithfullyFlat_arbitrary P hP f hf hdeg
  let := (g).toAlgebra
  let e : N ≃ₗ[R] PolynomialPerfectoidCandidate D d f hd :=
    { toFun := fun y => y
      invFun := fun y => y
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a y
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv K e hN

end SerrePositivity.BhattScholze.Andre

end ArbitraryPerfectPrismMonicPerfectoidCompletelyFlat
