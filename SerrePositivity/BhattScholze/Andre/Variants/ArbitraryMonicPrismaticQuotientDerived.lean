module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticQuotientDerived
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryMonicPrismaticCoefficientReduction

/-!
# André E1・E2（任意族）：モニック族の実自由 δ 源商上の導来還元

## 概要

任意モニック族の実導来還元は、作用を降下した raw (p,d) 剰余の single と同型。
BS Rem 7.15（著者版 p.62）の実係数商への比較。

## 方針

自由 δ 源から商への全射性で H⁰ の線形比較を降下し、ホモロジー消滅と正規化純対象比較を使う。
原典の Prop 7.11 を用いる証明とは異なる実関係による計算。

## 規約

モニック性、p 正則性、δ(d) の単元性を仮定する。正次数は不要。

## 使われ方

元の係数環の (p,d) 商へ制限して、実導来剰余の忠実平坦性へ接続する。
-/

@[expose] public noncomputable section
universe u
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
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
