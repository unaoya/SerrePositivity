module

public import SerrePositivity.BhattScholze.Andre.Variants.MonicPrismaticBoundedSupportTor
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionSourceResidueTensor

/-!
# André E1・E2：任意モニック族の実残余導来評価比較

## 概要

任意モニック族の実残余自由 δ 源の導来評価は、実 raw (p,d) 剰余の single に同型。
BS Rem 7.15（著者版 p.62）の実導来剰余比較。

## 方針

有界深さ有限部分族の余極限から得た全評価源の Tor 消滅を用いる。
標準導来 augmentation と通常残余テンソルの既存同型を合成する。
原典の Prop 7.11 を使う証明とは異なる具体的 PD 計算の経路。

## 規約

添字型全体の有限性と多項式の正次数は不要。p 正則性と δ(d) の単元性を明示する。

## 使われ方

元の A/(p,d) 上の実還元と完備化に、有限性のない入力を供給する。
-/

@[expose] public noncomputable section
universe u
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
使われ方：BS Rem 7.15（著者版 p.62）の係数側の実導来剰余比較。 -/
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
