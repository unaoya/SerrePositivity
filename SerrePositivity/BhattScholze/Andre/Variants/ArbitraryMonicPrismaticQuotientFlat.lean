module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticQuotientFlat
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryMonicPrismaticQuotientDerived

/-!
# André E1・E2（任意族）：実商還元の H⁰ の元の係数商上の忠実平坦性

## 概要

任意正次数モニック族の実自由 δ 源商上の導来還元の H⁰ は、元の A/(p,d) 上忠実平坦。
BS Rem 7.15（著者版 p.62）の係数作用を保つ剰余比較。

## 方針

H⁰ の実源商線形比較を係数商へ制限し、明示した raw 剰余の標準係数作用と一致させる。
原典の Prop 7.11 を用いる証明とは異なる経路の計算。

## 規約

一般 (p,d) 商に沿う実還元を使う。Koszul 還元との無条件な同一視はしない。

## 使われ方

元の係数環上の実導来還元の平坦性と、完備化後の離散性の入力。
-/

@[expose] public noncomputable section
universe u
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
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上の実導来剰余入力。 -/
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
