module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticFiniteResidueKoszul
public import SerrePositivity.BhattScholze.DeltaRootFamilySourceColimitTor
public import SerrePositivity.BhattScholze.DeltaDivisionSourceResidueTensor

/-!
# André E1・E2：有限モニック族の実残余導来評価比較

## 概要

有限モニック族について、一般 f/d 包の実残余自由 δ 源の導来評価は実 raw 剰余の single に同型。
BS Rem 7.15（著者版 p.62）の実導来剰余比較の評価側。

## 方針

各有限 δ 深さの Koszul Tor 消滅を既存 G7 に渡し、Tor 対称性と標準 augmentation で比較する。
原典の Prop 7.11 を使う経路とは異なる明示関係による計算。

## 規約

元の係数環への制限や完備化後の主張は含まない。正次数は不要。

## 使われ方

一般 f/d 包の実係数側導来還元と実 raw (p,d) 商との比較に接続する。
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
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => (fun t : σ => monicRelation (f t) t)
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₁" => RingHom.comp (Ideal.Quotient.mk K₁)
  (deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d))

include s in
/-- 概要：有限モニック添字について、実残余自由δ射に沿う全β評価環の正次数Torが零。
方針：有限 δ 深さの Tor 消滅を既存の逐次余極限と Tor 対称性で移す。
規約：有限添字型を明示的な全列挙で与える。正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の標準導来 augmentation の入力。 -/
theorem monicPrismaticResidueSource_tor_subsingleton
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E₁ c₁
    Subsingleton (SerrePositivity.TorAlg ψ₁ (i + 1) P₁) := by
  let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
  apply deltaDivisionEvaluationSourceFamily_tor_subsingleton E₁ c₁ s ψ₁ i
  intro N
  exact monicPrismaticFiniteResidueEvaluationFamilySource_tor_subsingleton D d f s N hf hpA v hv i

local notation "β₁" => deltaDivisionSourceEval E₁ c₁
local notation "Mψ" => baseChangeScalarModule ψ₁
local notation "Mβ" => baseChangeScalarModule β₁

include s in
/-- 概要：Tor対称性で、同じ実残余終域をβに沿って導来拡大するための消滅条件を得る。
方針：有限 δ 深さの Tor 消滅を既存の逐次余極限と Tor 対称性で移す。
規約：有限添字型を明示的な全列挙で与える。正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の標準導来 augmentation の入力。 -/
theorem monicPrismaticResidueSourceEval_torVanishing
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    scalarExtensionTorVanishing β₁ Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
      let : Subsingleton (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        monicPrismaticResidueSource_tor_subsingleton
          (D := D) (f := f) (s := s) (d := d) hf hpA v hv i
      have hz : IsZero (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso ψ₁ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars ψ₁).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso ψ₁ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT


local notation "Q₁" => L₁ ⧸ K₁
local notation "Res₁" => DeltaAdjoinDivisionResidue E₁ (MvPolynomial.C d) c₁

/-- 概要：有限モニック族の実残余終域の導来評価は raw (p,d) 商の次数零対象と標準同型。
方針：高次 Tor 消滅による標準 augmentation と、通常残余テンソルの既存同型を合成する。
規約：同じ元の自由 δ 源射と評価射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の係数側の実導来剰余比較。 -/
def monicPrismaticResidueSourceDerivedIso
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
    (monicPrismaticResidueSourceEval_torVanishing D d f s hf hpA v hv) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

end SerrePositivity.BhattScholze.Andre
