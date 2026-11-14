module

public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.BhattScholze.Andre.Envelope.RootResidueKoszul
public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete

/-!
# 根添加の源の導来還元と完備性

## 概要
二つの主元完備化の H⁰ と PD H⁰ の反射比較、根添加の残余全源 Tor・導来評価比較、係数側の導来還元と raw 残余商、商環上の還元と H⁰ の忠実平坦性、射影モデルの制限、(p,d) 還元、逐次主元完備化後の還元と導来完備性、冪零剰余射による還元、ghost 単射入力。
BS 著者版 Remark 7.15 の根の包を構成するため、根添加の源の導来還元と完備性を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/MonicSource`、`Envelope/RootFamilySource`、`Perfection/DeltaAlgebra`、`PowerRootEnvelope/Unconditional/Localization`、`PowerRootEnvelope/Unconditional/Source`、`RootEnvelope/PerfectPrism`、`RootEnvelope/RawCompletion`、`RootEnvelope/Source`、`Variants/RootedExtension`。
-/

universe u

/-! ## G7交換入力に相対的な根添加の実残余全源Tor

任意有限δ深さで証明した消滅を、実評価環へ移す。
G7の交換入力を保持し、実導来完備化後CFFや一般B4全射性は結論しない。
-/

@[expose] public noncomputable section DeltaRootResidueSourceColimitTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "α₀" => RingHom.comp (Ideal.Quotient.mk K₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀

/-- G7の実図式交換入力の下、根添加の実残余自由δ射に沿う全評価環の正次数Torが零。
交換入力は未解消として保持する。 -/
theorem deltaRootResidueSource_tor_subsingleton_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ)
    (hpres : PreservesColimit F₀ ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
    Subsingleton (SerrePositivity.TorAlg α₀ (i + 1) P₀) := by
  let := deltaDivisionSourceEvaluationAlgebra E₀ c₀
  exact deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit E₀ c₀ α₀ i
    (fun N => deltaRootFiniteResidueSource_tor_subsingleton D d b hpA hg v hv N i) hpres

end SerrePositivity.BhattScholze

end DeltaRootResidueSourceColimitTor

/-! ## G7入力に相対的な根添加の実残余導来評価比較

既存Tor対称性と標準導来添加写像を使う。係数側Koszul操作との比較や
実導来完備化後CFFは別工程。
-/

@[expose] public noncomputable section DeltaRootResidueSourceDerived

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀

/-- G7交換入力の下、実評価βに沿う実残余終域の全高次Torは零。 -/
theorem deltaRootResidueSourceEval_torVanishing_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    scalarExtensionTorVanishing β₀ Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvaluationAlgebra E₀ c₀
      let : Subsingleton (((ModuleCat.extendScalars ψ₀).leftDerived (i + 1)).obj Mβ) :=
        deltaRootResidueSource_tor_subsingleton_of_preservesColimit D d b hpA hg v hv i (hpres i)
      have hz : IsZero (((ModuleCat.extendScalars ψ₀).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso ψ₀ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars ψ₀).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso ψ₀ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT

/-- 実評価による通常係数拡大と、標準残余源作用の通常テンソルとの係数同値。 -/
def deltaRootResidueSourceEvalScalarEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    letI : Module L₀ Q₀ := Algebra.toModule
    ((ModuleCat.extendScalars β₀).obj Mψ) ≃ₗ[P₀] (P₀ ⊗[L₀] Q₀) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  letI : Module L₀ Q₀ := Algebra.toModule
  exact
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- G7入力の下で、実残余終域のβに沿う導来拡大は既存raw(p,d)商の次数零対象。 -/
def deltaRootResidueSourceDerivedIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  letI : Module L₀ Q₀ := Algebra.toModule
  let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₀ Mψ
    (deltaRootResidueSourceEval_torVanishing_of_preservesColimit D d b hpA hg v hv hpres) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- 導来比較の順射は、標準導来添加写像と具体的な残余商比較の合成そのもの。 -/
theorem deltaRootResidueSourceDerivedIso_hom_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    letI : Module L₀ Q₀ := Algebra.toModule
    let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
      (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
    (deltaRootResidueSourceDerivedIso_of_preservesColimit D d b hpA hg v hv hpres).hom.hom =
      (boundedAboveDerivedBaseChangeModuleAugmentation β₀).app Mψ ≫
        (boundedAboveDerivedSingleFunctor.map e.toModuleIso.hom).hom := by
  rfl

end SerrePositivity.BhattScholze

end DeltaRootResidueSourceDerived

/-! ## 根添加の係数側実導来還元とraw残余商の比較

既存三因子の実導来対象を使い、G7交換入力に相対的な残余評価比較へ接続する。
導来完備化やperfectionの後の完全忠実平坦性は含まない。
-/

@[expose] public noncomputable section DeltaRootSourceCoefficientResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)

/-- 既存の実テンソルで与えた、根添加の具体的な係数商還元対象。 -/
abbrev DeltaRootSourceCoefficientReduced :=
  boundedAboveDerivedTensor.obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
        derivedBaseChangeScalarObject q₀)

/-- G7入力の下、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。 -/
def deltaRootSourceCoefficientResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    DeltaRootSourceCoefficientReduced D d b ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ (MvPolynomial.C d) c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (deltaRootResidueSourceDerivedIso_of_preservesColimit D d b hpA hg v hv hpres)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。 -/
def deltaRootSourceCoefficientResidueHomologyZeroIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaRootSourceCoefficientResidueIso_of_preservesColimit D d b hpA hg v hv hpres))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。 -/
theorem deltaRootSourceCoefficientResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootSourceCoefficientResidueIso_of_preservesColimit D d b hpA hg v hv hpres)))

end SerrePositivity.BhattScholze

end DeltaRootSourceCoefficientResidue

/-! ## 実商環上の根添加導来還元

(p,d)の通常商への実基底変更を扱う。Koszul還元との同一視や完備化後の
完全平坦性は主張せず、G7の具体的交換入力を明示して保持する。
-/

@[expose] public noncomputable section DeltaRootSourceQuotientDerived

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ (MvPolynomial.C d) c₀
local notation "r₀" => Ideal.Quotient.mk
  (deltaAdjoinDivisionResidueIdeal E₀ (MvPolynomial.C d) c₀)

/-- 実二因子導来テンソルを実商環Q上へ基底変更した対象。 -/
abbrev DeltaRootSourceQuotientDerived :=
  (boundedAboveDerivedBaseChange q₀).obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα))

/-- raw残余商上のβを経由する源作用の、実商環への標準降下。 -/
def deltaRootSourceQuotientResidueMap : Q₀ →+* Res₀ :=
  Ideal.Quotient.lift K₀ ((r₀).comp ((j₀).comp β₀)) (by
    change K₀ ≤ RingHom.ker ((r₀).comp ((j₀).comp β₀))
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change r₀ ((j₀).comp β₀ (p : L₀)) = 0
      rw [map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert _ _))
    · have hx := Set.mem_singleton_iff.mp hx
      subst x
      change r₀ (j₀ (β₀ (MvPolynomial.C (MvPolynomial.C d)))) = 0
      rw [deltaDivisionSourceEval_C]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

omit [Unique σ] in
/-- 商代表元の作用は、β、raw係数射、残余商射の合成である。 -/
theorem deltaRootSourceQuotientResidueMap_mk (x : L₀) :
    deltaRootSourceQuotientResidueMap D d b (q₀ x) = r₀ (j₀ (β₀ x)) := rfl

/-- 商環作用をqで制限すると、前工程のβによる実L加群になる。 -/
def deltaRootSourceQuotientResidueRestrictionIso :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Res₀)) ≅ MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact
    { hom := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change r₀ (j₀ (β₀ r)) * x = (β₀ r) • x
            rw [Algebra.smul_def]
            rfl } }
      inv := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change (β₀ r) • x = r₀ (j₀ (β₀ r)) * x
            rw [Algebra.smul_def]
            rfl } }
      hom_inv_id := by rfl
      inv_hom_id := by rfl }

/-- 実商環上の基底変更を制限すると、既存の実三因子還元に一致する。 -/
def deltaRootSourceQuotientDerivedRestrictionIso :
    (boundedAboveDerivedRestrictScalars q₀).obj
        (DeltaRootSourceQuotientDerived D d b) ≅ DeltaRootSourceCoefficientReduced D d b :=
  (boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app _

/-- 実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。 -/
def deltaRootSourceQuotientDerivedRestrictedH0Iso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (DeltaRootSourceQuotientDerived D d b).obj) ≅ MRes :=
  ((derivedRestrictScalarsHomologyIso q₀ 0).app
      (DeltaRootSourceQuotientDerived D d b).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceQuotientDerivedRestrictionIso D d b)) ≪≫
    deltaRootSourceCoefficientResidueHomologyZeroIso_of_preservesColimit
      D d b hpA hg v hv hpres

/-- G7入力の下、実商環上の還元そのものの非零次数ホモロジーが消える。 -/
theorem deltaRootSourceQuotientDerived_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (DeltaRootSourceQuotientDerived D d b).obj) := by
  have hz := deltaRootSourceCoefficientResidue_homology_isZero_of_preservesColimit
    D d b hpA hg v hv hpres i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (deltaRootSourceQuotientDerivedRestrictionIso D d b)))
  have hr := (derivedRestrictScalarsHomologyIso q₀ i).app
    (DeltaRootSourceQuotientDerived D d b).obj
  have hs := hr.isZero_iff.mp hz'
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (DeltaRootSourceQuotientDerived D d b).obj) :=
    ModuleCat.subsingleton_of_isZero (R := L₀) hs
  exact ModuleCat.isZero_of_subsingleton _

/-- 実商環上でのH0同型。qの全射性により、L線形比較を実Q線形比較へ昇格する。 -/
def deltaRootSourceQuotientDerivedH0Iso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (DeltaRootSourceQuotientDerived D d b).obj) ≅ ModuleCat.of Q₀ Res₀ := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := deltaRootSourceQuotientDerivedRestrictedH0Iso_of_preservesColimit
    D d b hpA hg v hv hpres ≪≫ (deltaRootSourceQuotientResidueRestrictionIso D d b).symm
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

end SerrePositivity.BhattScholze

end DeltaRootSourceQuotientDerived

/-! ## 実商還元のH0の元の係数商上の忠実平坦性

通常(p,d)商への実導来基底変更を扱う。一般のKoszul還元と同一視しない。
-/

@[expose] public noncomputable section DeltaRootSourceQuotientFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "k₀" => Ideal.span {(p : A), d}
local notation "κ₀" => Ideal.Quotient.mk k₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀

/-- 元の係数商から実源商への、二重係数包含の標準降下。 -/
def deltaRootSourceQuotientCoefficientMap : A ⧸ k₀ →+* Q₀ :=
  Ideal.Quotient.lift k₀ ((q₀).comp
    ((MvPolynomial.C : P₀ →+* L₀).comp (MvPolynomial.C : A →+* P₀))) (by
      change k₀ ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · subst x
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_insert _ _))
      · have hx := Set.mem_singleton_iff.mp hx
        subst x
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

omit [Fact p.Prime] [Unique σ] in
/-- 係数商代表元は、実源の二重係数包含の標準商像に送られる。 -/
theorem deltaRootSourceQuotientCoefficientMap_mk (a : A) :
    deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d (κ₀ a) =
      q₀ (MvPolynomial.C (MvPolynomial.C a)) := rfl

omit [Unique σ] in
/-- 実商環を経由する係数射は、既存raw残余商への標準係数射そのもの。 -/
theorem deltaRootSourceQuotientCoefficientMap_comp_residue
    (hpP : Function.Injective (fun x : P₀ => (p : P₀) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (deltaRootSourceQuotientResidueMap D d b).comp
        (deltaRootSourceQuotientCoefficientMap (σ := σ) d) =
      deltaRootAdjoinDivisionResidueBaseMap D d b hpP hpL hg v hv := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  change deltaRootSourceQuotientResidueMap D d b
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) =
    deltaRootAdjoinDivisionResidueBaseMap D d b hpP hpL hg v hv (κ₀ a)
  rw [deltaRootSourceQuotientCoefficientMap_mk, deltaRootSourceQuotientResidueMap_mk,
    deltaDivisionSourceEval_C, deltaRootAdjoinDivisionResidueBaseMap_mk]

set_option maxHeartbeats 800000 in
-- 実商環上のホモロジーと複数の商作用を同時に照合するため。
/-- G7交換入力の下、実導来商還元のH0は元のA/(p,d)上忠実平坦。 -/
theorem deltaRootSourceQuotientDerivedH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat (A ⧸ k₀)
      ((ModuleCat.restrictScalars (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (DeltaRootSourceQuotientDerived D d b).obj)) := by
  have hpP : Function.Injective (fun x : P₀ => (p : P₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₀)
    have h' : IsSMulRegular P₀ (p : P₀) := by simpa only [map_natCast] using h
    exact h'
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    have h := (show IsSMulRegular P₀ (p : P₀) from hpP).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    exact h'
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpP hpL hg v hv
  let H := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
    (DeltaRootSourceQuotientDerived D d b).obj
  let M := (ModuleCat.restrictScalars
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj H
  let eQ := deltaRootSourceQuotientDerivedH0Iso_of_preservesColimit D d b hpA hg v hv hpres
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
          deltaRootSourceQuotientResidueMap D d b
            (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) * eQ.hom.hom x at h
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          deltaRootSourceQuotientResidueMap_mk, deltaDivisionSourceEval_C] at h
        change eQ.hom.hom ((deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          deltaRootAdjoinDivisionResidueBaseMap D d b hpP hpL hg v hv (κ₀ a) * eQ.hom.hom x
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          deltaRootAdjoinDivisionResidueBaseMap_mk]
        exact h }
  have := deltaRootAdjoinDivisionResidue_moduleFaithfullyFlat D d b hpP hpL hg v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e

end SerrePositivity.BhattScholze

end DeltaRootSourceQuotientFlat

/-! ## 根添加の実商還元とraw商の正規化導来同型

既存の純対象比較を再利用し、実商環上のH0計算を導来対象の比較へ昇格する。
-/

@[expose] public noncomputable section DeltaRootSourceQuotientSingle

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => DeltaRootSourceQuotientDerived D d b

/-- 実商還元は、明示したG7入力の下で標準t構造の非負部分に属する。 -/
theorem deltaRootSourceQuotientDerived_isGE_zero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact deltaRootSourceQuotientDerived_homology_isZero_of_preservesColimit
    D d b hpA hg v hv hpres i (by omega)

/-- 同じ入力の下で標準t構造の非正部分にも属する。 -/
theorem deltaRootSourceQuotientDerived_isLE_zero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact deltaRootSourceQuotientDerived_homology_isZero_of_preservesColimit
    D d b hpA hg v hv hpres i (by omega)

/-- 実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。 -/
def deltaRootSourceQuotientDerivedSingleIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := deltaRootSourceQuotientDerived_isGE_zero_of_preservesColimit D d b hpA hg v hv hpres
  have := deltaRootSourceQuotientDerived_isLE_zero_of_preservesColimit D d b hpA hg v hv hpres
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (X₀).obj 0) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (deltaRootSourceQuotientDerivedH0Iso_of_preservesColimit D d b hpA hg v hv hpres)

/-- この導来同型のH0は、前工程で構成した具体的な商環線形同型そのもの。 -/
theorem deltaRootSourceQuotientDerivedSingleIso_homologyZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
        (deltaRootSourceQuotientDerivedSingleIso_of_preservesColimit
          D d b hpA hg v hv hpres).hom.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q₀) 0).hom.app
        (ModuleCat.of Q₀ Res₀) =
      (deltaRootSourceQuotientDerivedH0Iso_of_preservesColimit D d b hpA hg v hv hpres).hom := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  have := deltaRootSourceQuotientDerived_isGE_zero_of_preservesColimit D d b hpA hg v hv hpres
  have := deltaRootSourceQuotientDerived_isLE_zero_of_preservesColimit D d b hpA hg v hv hpres
  let e := deltaRootSourceQuotientDerivedH0Iso_of_preservesColimit D d b hpA hg v hv hpres
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q₀) 0).hom.naturality
    e.hom
  change (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat Q₀) 0).map e.hom) ≫ _ = _ at hn
  change (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
    ((normalizedPureHomologyIso (X₀).obj 0).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat Q₀) 0).map e.hom) ≫ _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    normalizedPureHomologyIso_homology, Category.id_comp]
  rfl

end SerrePositivity.BhattScholze

end DeltaRootSourceQuotientSingle

/-! ## 実根添加源の射影モデルの元の係数環への制限

源の二重多項式構造を使う。任意の環射について射影性を保存するとは主張しない。
-/

@[expose] public noncomputable section DeltaRootSourceCoefficientModels

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => MvPolynomial (σ × ℕ) P₀
local notation "C₀" => algebraMap A L₀

/-- 二重多項式源上の射影加群は、二重係数包含に沿う実係数制限でも射影的。 -/
theorem deltaRootSourceCoefficientRestrict_projective (M : ModuleCat.{u} L₀) [Projective M] :
    Projective ((ModuleCat.restrictScalars C₀).obj M) := by
  let : Module.Free A L₀ := Module.Free.trans (R := A) (S := P₀) (M := L₀)
  have : Module.Projective L₀ M := inferInstance
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := L₀) (P := M)).mp inferInstance
  let F := ModuleCat.restrictScalars C₀
  let Y := ModuleCat.of L₀ (M →₀ L₀)
  let i : M ⟶ Y := ModuleCat.ofHom s
  let r : Y ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination L₀ id)
  have hir : i ≫ r = 𝟙 M := ModuleCat.hom_ext hs
  let e : F.obj Y ≃ₗ[A] (M →₀ L₀) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (M →₀ L₀) at x
        apply Finsupp.ext
        intro m
        change (algebraMap A L₀ r) * x m = r • x m
        rw [Algebra.smul_def] }
  have : Module.Projective A (F.obj Y) := Module.Projective.of_equiv e.symm
  have hM : Module.Projective A (F.obj M) :=
    Module.Projective.of_split (F.map i).hom (F.map r).hom (by
      apply ModuleCat.hom_ext_iff.mp
      change F.map i ≫ F.map r = 𝟙 (F.obj M)
      rw [← F.map_comp, hir, F.map_id])
  exact ModuleCat.projective_of_categoryTheory_projective (F.obj M)

/-- 指定した実源射影モデルを、実A係数制限対象の射影モデルへ変換する。 -/
def deltaRootSourceCoefficientModel
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    BoundedAboveDerivedModel (((boundedAboveDerivedRestrictScalars C₀).obj X).obj) where
  complex := ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex
  bound := P.bound
  bounded := inferInstance
  projective i := deltaRootSourceCoefficientRestrict_projective (P.complex.X i)
  iso := (boundedAboveDerivedRestrictScalarsModelIso C₀ X P).symm

/-- 元の係数環の任意イデアルでの実導来還元を、制限した具体的射影モデルで計算する。 -/
def deltaRootSourceCoefficientQuotientModelIso (I : Ideal A)
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X)).obj ≅
      DerivedCategory.Q.obj (baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex)) :=
  boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk I) _
    (deltaRootSourceCoefficientModel X P)

end SerrePositivity.BhattScholze

end DeltaRootSourceCoefficientModels

/-! ## 実源の通常加群の係数商比較

既存の商加群・拡張イデアル・係数制限を使い、標準商像を保って比較する。
-/

@[expose] public noncomputable section DeltaRootSourceCoefficientSquare

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => MvPolynomial (σ × ℕ) P₀
local notation "C₀" => algebraMap A L₀
variable (I : Ideal A)
local notation "J₀" => Ideal.map C₀ I
local notation "κ₀" => algebraMap (A ⧸ I) (L₀ ⧸ J₀)
attribute [local instance] adicQuotientAlgebra

/-- 二重多項式源の拡張イデアルによる作用部分加群は、元の係数イデアルの作用に一致する。 -/
theorem deltaRootSourceCoefficientIdeal_smul_restrict (M : ModuleCat.{u} L₀) :
    letI := Module.compHom M C₀
    letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    (J₀ • (⊤ : Submodule L₀ M)).restrictScalars A = I • (⊤ : Submodule A M) := by
  let := Module.compHom M C₀
  let : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Submodule.restrictScalars_map_smul_eq I ⊤

/-- Aへ制限してから係数商を取る操作と、Lで拡張イデアルの商を取る操作の標準同型。 -/
def deltaRootSourceCoefficientQuotientModuleIso (M : ModuleCat.{u} L₀) :
    (quotientModuleFunctor I).obj ((ModuleCat.restrictScalars C₀).obj M) ≅
      (ModuleCat.restrictScalars κ₀).obj ((quotientModuleFunctor J₀).obj M) := by
  letI := Module.compHom M C₀
  letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA := (Submodule.quotEquivOfEq _ _
    (deltaRootSourceCoefficientIdeal_smul_restrict I M).symm).trans
      (Submodule.Quotient.restrictScalarsEquiv A (J₀ • (⊤ : Submodule L₀ M)))
  refine ModuleCat.isoMk eA.toAddEquiv.toAddCommGrpIso ?_
  intro s
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  ext x
  exact (eA.map_smul a x).symm

/-- 標準商像を保つ通常係数商比較の公式。 -/
theorem deltaRootSourceCoefficientQuotientModuleIso_mk (M : ModuleCat.{u} L₀) (x : M) :
    (deltaRootSourceCoefficientQuotientModuleIso I M).hom
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  rfl

/-- この係数商比較は実源加群の任意の射に自然。 -/
def deltaRootSourceCoefficientQuotientModuleNatIso :
    ModuleCat.restrictScalars C₀ ⋙ quotientModuleFunctor I ≅
      quotientModuleFunctor J₀ ⋙ ModuleCat.restrictScalars κ₀ := by
  refine NatIso.ofComponents (deltaRootSourceCoefficientQuotientModuleIso I) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change (deltaRootSourceCoefficientQuotientModuleIso I N).hom
        (Submodule.Quotient.mk (f.hom x)) =
          ((ModuleCat.restrictScalars κ₀).map ((quotientModuleFunctor J₀).map f))
            ((deltaRootSourceCoefficientQuotientModuleIso I M).hom (Submodule.Quotient.mk x))
      rw [deltaRootSourceCoefficientQuotientModuleIso_mk,
        deltaRootSourceCoefficientQuotientModuleIso_mk]
      rfl

/-- 同じ通常商比較を、実際の通常係数拡大関手の自然同型として表す。 -/
def deltaRootSourceCoefficientScalarExtensionNatIso :
    ModuleCat.restrictScalars C₀ ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅
      ModuleCat.extendScalars (Ideal.Quotient.mk J₀) ⋙ ModuleCat.restrictScalars κ₀ :=
  Functor.isoWhiskerLeft _ (quotientScalarExtensionIso I) ≪≫
    deltaRootSourceCoefficientQuotientModuleNatIso I ≪≫
      Functor.isoWhiskerRight (quotientScalarExtensionIso J₀).symm _

/-- 実源の任意の複体について、通常の係数商比較を項ごとに適用する。 -/
def deltaRootSourceCoefficientCochainSquareIso
    (K : CochainComplex (ModuleCat.{u} L₀) ℤ) :
    baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars κ₀).mapHomologicalComplex (.up ℤ)).obj
        (baseChange (Ideal.Quotient.mk J₀) K) :=
  (Functor.mapHomologicalComplexCompIso
    (deltaRootSourceCoefficientScalarExtensionNatIso I) (.up ℤ)).app K

attribute [local instance] HasDerivedCategory.standard

/-- 元の係数商への実導来還元は、実源商での還元を係数制限した対象と同型。
具体的源のA自由性から制限射影モデルを供給し、Tor仮定は追加しない。 -/
def deltaRootSourceCoefficientDerivedSquareIso
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J₀)).obj X) :=
  ObjectProperty.isoMk _
    (deltaRootSourceCoefficientQuotientModelIso I X P ≪≫
      DerivedCategory.Q.mapIso (deltaRootSourceCoefficientCochainSquareIso I P.complex) ≪≫
        ((derivedRestrictScalarsFactors κ₀).app
          (baseChange (Ideal.Quotient.mk J₀) P.complex)).symm ≪≫
        (derivedRestrictScalars κ₀).mapIso
          (boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk J₀) X P).symm)

end SerrePositivity.BhattScholze

end DeltaRootSourceCoefficientSquare

/-! ## 元の(p,d)係数商への実根添加導来還元

拡張イデアルと降下係数射を照合し、二つの実導来還元の比較を具体的な型へ特殊化する。
-/

@[expose] public noncomputable section DeltaRootSourcePDReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "C₀" => algebraMap A L₀
variable (d : A)
local notation "I₀" => Ideal.span {(p : A), d}
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d

omit [Fact p.Prime] in
/-- 元の(p,d)の二重係数包含に沿う拡張は、実源の(p,C(Cd))に一致する。 -/
theorem deltaRootSourcePDIdeal_map : Ideal.map C₀ I₀ = K₀ := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]
  rfl

/-- 任意の実源上の実導来対象について、元の(p,d)還元と実源商での還元を結ぶ。 -/
def deltaRootSourcePDDerivedSquareIso
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) := by
  let F (J : Ideal L₀) :=
    Σ' h : I₀ ≤ J.comap C₀,
      letI := Ideal.Quotient.algebraQuotientOfLEComap h
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
          ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
        (boundedAboveDerivedRestrictScalars (algebraMap (A ⧸ I₀) (L₀ ⧸ J))).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).obj X)
  let e : F ((I₀).map C₀) :=
    ⟨Ideal.le_comap_map, deltaRootSourceCoefficientDerivedSquareIso I₀ X P⟩
  let e' : F K₀ := Eq.mp (congrArg F (deltaRootSourcePDIdeal_map (σ := σ) (p := p) d)) e
  letI := Ideal.Quotient.algebraQuotientOfLEComap e'.1
  have hκ : algebraMap (A ⧸ I₀) (L₀ ⧸ K₀) = κ₀ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    rfl
  have he := e'.2
  simpa only [hκ] using he

variable [Unique σ] (D : DeltaStructure p A) (b : σ → A)
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)

/-- 実根添加二因子導来対象の、元の係数環Aへの実制限対象。 -/
abbrev DeltaRootSourceCoefficientObject :=
  (boundedAboveDerivedRestrictScalars C₀).obj X₀

set_option maxHeartbeats 800000 in
-- 二つの実係数作用を持つテンソルモデルと既存還元対象の型を同時に照合するため。
/-- 元のA/(p,d)での実導来還元と、既存の実源商上の根添加還元の比較。 -/
def deltaRootSourceCoefficientPDReductionIso :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        (DeltaRootSourceCoefficientObject d D b) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj (DeltaRootSourceQuotientDerived D d b) :=
  deltaRootSourcePDDerivedSquareIso (p := p) (A := A) (σ := σ) d X₀
    (boundedAboveDerivedTensorModel
      (boundedAboveDerivedSingleFunctor.obj Mβ) (boundedAboveDerivedSingleFunctor.obj Mα))

end SerrePositivity.BhattScholze

end DeltaRootSourcePDReduction

/-! ## 元の係数環上の実(p,d)還元とraw残余商

実源商でのG7相対的比較を元の係数環へ渡す。一般Koszul還元や完備化後CFFは含まない。
-/

@[expose] public noncomputable section DeltaRootSourcePDResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)) (DeltaRootSourceCoefficientObject d D b)
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 元のA上の実根添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。 -/
def deltaRootSourceCoefficientPDResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact deltaRootSourceCoefficientPDReductionIso d D b ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (deltaRootSourceQuotientDerivedSingleIso_of_preservesColimit D d b hpA hg v hv hpres) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。 -/
def deltaRootSourceCoefficientPDResidueH0Iso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootSourceCoefficientPDResidueIso_of_preservesColimit D d b hpA hg v hv hpres)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 元のA上の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem deltaRootSourceCoefficientPDResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootSourceCoefficientPDResidueIso_of_preservesColimit D d b hpA hg v hv hpres)))

/-- 元のA上の実(p,d)還元のH0は、実係数商A/(p,d)上忠実平坦。 -/
theorem deltaRootSourceCoefficientPDResidueH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars κ₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (DeltaRootSourceQuotientDerived D d b).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceCoefficientPDReductionIso d D b)) ≪≫
    (derivedRestrictScalarsHomologyIso κ₀ 0).app (DeltaRootSourceQuotientDerived D d b).obj
  have := deltaRootSourceQuotientDerivedH0_faithfullyFlat_of_preservesColimit
    D d b hpA hg v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootSourcePDResidue

/-! ## 実根添加対象の逐次主元完備化後の(p,d)還元

既存の二つの主元完備化を逐次適用した具体的対象を扱う。
原典の(p,d)完備化・環H0候補との比較や離散性は別工程である。
-/

@[expose] public noncomputable section DeltaRootSourceIteratedCompletionResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => DeltaRootSourceCoefficientObject d D b
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 既存の実p完備化の後に既存の実d完備化を施した具体的根添加対象。 -/
abbrev DeltaRootSourceIteratedPDCompletion := (Cd).obj ((Cp).obj X₀)

/-- p,dが個別に正則なら、この逐次対象の実(p,d)還元は元の実還元と同型。 -/
def deltaRootSourceIteratedPDReductionIso
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b) ≅
      (boundedAboveDerivedBaseChange q₀).obj X₀ :=
  prismaticCoefficientIteratedCompletionPairIso (p : A) d hpA hd X₀

omit [Unique σ] in
/-- 還元比較は、元の対象からの合成標準完備化単位の像の左逆となる。 -/
theorem deltaRootSourceIteratedPDReductionIso_unit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (deltaRootSourceIteratedPDReductionIso D d b hpA hd).hom = 𝟙 _ :=
  prismaticCoefficientIteratedCompletionPairIso_unit (p : A) d hpA hd X₀

/-- G7入力の下、逐次主元完備化後の実還元は標準作用付きraw残余商のsingle対象。 -/
def deltaRootSourceIteratedPDResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b) ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact deltaRootSourceIteratedPDReductionIso D d b hpA hd ≪≫
    deltaRootSourceCoefficientPDResidueIso_of_preservesColimit D d b hpA hg v hv hpres

/-- raw比較は合成標準単位の実還元を、未完備対象のraw比較へ送る。 -/
theorem deltaRootSourceIteratedPDResidueIso_unit_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (deltaRootSourceIteratedPDResidueIso_of_preservesColimit D d b hpA hd hg v hv hpres).hom =
      (deltaRootSourceCoefficientPDResidueIso_of_preservesColimit D d b hpA hg v hv hpres).hom := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  simp only [deltaRootSourceIteratedPDResidueIso_of_preservesColimit, Iso.trans_hom]
  rw [← Category.assoc, deltaRootSourceIteratedPDReductionIso_unit, Category.id_comp]

/-- 逐次主元完備化後の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem deltaRootSourceIteratedPDResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b)).obj) :=
  (deltaRootSourceCoefficientPDResidue_homology_isZero_of_preservesColimit
    D d b hpA hg v hv hpres i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (deltaRootSourceIteratedPDReductionIso D d b hpA hd)))

/-- 逐次主元完備化後の実(p,d)還元のH0は、標準A/(p,d)上で忠実平坦。 -/
theorem deltaRootSourceIteratedPDResidueH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀ ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (DeltaRootSourceIteratedPDCompletion D d b)).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b)).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceIteratedPDReductionIso D d b hpA hd))
  have := deltaRootSourceCoefficientPDResidueH0_faithfullyFlat_of_preservesColimit
    D d b hpA hg v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootSourceIteratedCompletionResidue

/-! ## 具体的逐次根添加対象の冪零剰余射による実還元

実A/(p,dⁿ)還元の後に実冪零剰余射を施した対象を計算する。
A/(p,dⁿ)上の離散性・平坦性自体はG10の別工程である。
-/

@[expose] public noncomputable section DeltaRootSourcePowerResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "qₙ" =>
  Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))
local notation "rₙ" => prismaticPowerResidueMap (p : A) d n hn
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange rₙ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀)

/-- 実冪剰余の実冪零還元は、既存の標準係数作用付きraw商のsingle対象。 -/
def deltaRootSourcePowerResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Z₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm ≪≫
    deltaRootSourceIteratedPDResidueIso_of_preservesColimit D d b hpA hd hg v hv hpres

/-- 実冪剰余の実冪零還元の非零次数ホモロジーは零。 -/
theorem deltaRootSourcePowerResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Z₀).obj) :=
  (deltaRootSourceIteratedPDResidue_homology_isZero_of_preservesColimit
    D d b hpA hd hg v hv hpres i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm))

/-- 実冪零還元のH0はA/(p,d)上忠実平坦。冪剰余環上の平坦性とは区別する。 -/
theorem deltaRootSourcePowerResidueH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm)
  have := deltaRootSourceIteratedPDResidueH0_faithfullyFlat_of_preservesColimit
    D d b hpA hd hg v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootSourcePowerResidue

/-! ## 具体的根添加対象のG10標準冪零還元入力

標準商環上での次数零集中とH0忠実平坦性を供給する。
冪零厚化前の対象の離散性・平坦性はG10の別工程である。
-/

@[expose] public noncomputable section DeltaRootSourceCanonicalPowerResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
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

/-- G10の標準冪零商による実還元は、商環上の標準raw加群のsingle対象。 -/
def deltaRootSourceCanonicalPowerResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    W₀ ≅ boundedAboveDerivedSingleFunctor.obj MCan := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      (deltaRootSourcePowerResidueIso_of_preservesColimit D d b n hn hpA hd hg v hv hpres) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso (eₙ).toRingHom 0).app MRes)

include hn in
/-- 標準冪零商による実還元の非零次数ホモロジーは零。 -/
theorem deltaRootSourceCanonicalPowerResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MCan i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootSourceCanonicalPowerResidueIso_of_preservesColimit
          D d b n hn hpA hd hg v hv hpres)))

include hn in
/-- 標準冪零商による実還元のH0は、その正確な商環上で忠実平坦。 -/
theorem deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
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
  have : Module.FaithfullyFlat R₀ M :=
    deltaRootSourcePowerResidueH0_faithfullyFlat_of_preservesColimit
      D d b n hn hpA hd hg v hv hpres
  have : Module.FaithfullyFlat Sₙ M := Module.FaithfullyFlat.trans Sₙ R₀ M
  exact Module.FaithfullyFlat.of_linearEquiv Sₙ M eH.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootSourceCanonicalPowerResidue

/-! ## G4による具体的根添加源のghost単射入力

G10の標準還元の入口から独立のghost単射仮定を除く。
G7の具体的colimit交換入力は明示して保持する。
-/

@[expose] public noncomputable section DeltaRootSourceRegularGhost

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ

/-- 元の係数環のp正則性から、実自由δ源上のghost単射をG4で供給する。 -/
theorem deltaRootSource_ghostMap_injective
    (hpA : Function.Injective (fun x : A => (p : A) * x)) :
    Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀) := by
  apply witt_ghostMap_injective_of_mul_prime_injective
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)

variable [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "J₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk J₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Sₙ" => Tₙ ⧸ Kₙ
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))))) X₀
local notation "W₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀

include hn in
/-- G7入力の下、ghost仮定なしでG10の標準還元の次数消滅を得る。 -/
theorem deltaRootSourceCanonicalPowerResidue_homology_isZero_of_p_regular
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) :=
  deltaRootSourceCanonicalPowerResidue_homology_isZero_of_preservesColimit
    D d b n hn hpA hd (deltaRootSource_ghostMap_injective (σ := σ) hpA) v hv hpres i hi

include hn in
/-- G7入力の下、ghost仮定なしでG10の標準還元H0の忠実平坦性を得る。 -/
theorem deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat_of_p_regular
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj) :=
  deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat_of_preservesColimit
    D d b n hn hpA hd (deltaRootSource_ghostMap_injective (σ := σ) hpA) v hv hpres

end SerrePositivity.BhattScholze

end DeltaRootSourceRegularGhost

/-! ## BSの二つの実主元完備化H0と実PD H0の共有反射比較 -/

@[expose] public noncomputable section IteratedPDH0Reflection

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (f d : R)
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat R) 0) (ModuleCat.of R R)
local notation "Y" => CategoryTheory.Functor.obj (derivedComplexCompletionFunctor R f) M

/-- BSで使う元のp,d逐次実完備化対象。 -/
abbrev IteratedPDCompletionObject := (derivedComplexCompletionFunctor R d).obj Y

local notation "Z" => IteratedPDCompletionObject R f d
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat R) 0)
local notation "U" => CategoryTheory.NatTrans.app (derivedComplexCompletionUnit R f) M ≫
  CategoryTheory.NatTrans.app (derivedComplexCompletionUnit R d) Y

/-- raw自身の実逐次完備化から誘導される、元のRaw線形標準単位。 -/
def iteratedPDH0Unit : R →ₗ[R] H Z :=
  (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
    (ModuleCat.of R R)) ≫ (DerivedCategory.homologyFunctor (ModuleCat R) 0).map U).hom

/-- raw自身の実逐次対象は、二つ目の完備化後にも最初の座標について完備。 -/
theorem iteratedPDCompletion_isComplete_first : IsComplete R f Z := by
  have hY : IsComplete R f Y := derivedComplexCompletionFunctor_isComplete R f M
  let K := DerivedCategory.Q.objPreimage Y
  let eK : DerivedCategory.Q.obj K ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  have hK := isComplete_of_iso R f eK.symm hY
  have hstage (n : ℕ) : IsComplete R f
      (DerivedCategory.Q.obj (complexPowerKoszulStage R d K n)) :=
    isComplete_Q_mappingCone R f (smulId (d ^ n) K) hK hK
  have hC := isComplete_complexTowerHomotopyLimitObject_of_stages R f
    (complexPowerKoszulStage R d K) (complexPowerKoszulTransition R d K) hstage
  let e : complexCompletionObject R d K ≅ Z :=
    (derivedComplexCompletionComparison R d).symm.app K ≪≫
      (derivedComplexCompletionFunctor R d).mapIso eK
  exact isComplete_of_iso R f e hC

/-- raw自身の実逐次H0は両座標について導来完備。 -/
theorem iteratedPDH0_isComplete :
    ∀ j : Fin 2, IsModuleComplete R (pairKoszulCoordinates R f d j) (H Z) := by
  intro j
  fin_cases j
  · exact isComplete_homology_isModuleComplete R f Z
      (iteratedPDCompletion_isComplete_first R f d) 0
  · exact derivedComplexCompletionFunctor_homology_isModuleComplete R d Y 0

/-- 同じ標準単位は、両座標について完備な加群への写像を一意に決定する。 -/
theorem iteratedPDH0_isCompleteModuleReflection :
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d) (H Z)
      (iteratedPDH0Unit R f d 1) where
  isComplete := iteratedPDH0_isComplete R f d
  universal N hN := by
    have hp : IsModuleComplete R f N := by simpa [pairKoszulCoordinates] using hN 0
    have hd : IsModuleComplete R d N := by
      simpa only [pairKoszulCoordinates, Fin.snoc_last] using hN (Fin.last 1)
    have hM : (M).IsLE 0 := inferInstance
    let := hM
    let := derivedComplexCompletionFunctor_isLE R f M 0 hM
    let eqv := ModuleCat.homEquiv.symm |>.trans
      (completionH0HomEquiv R d Y N hd) |>.trans
      (completionH0HomEquiv R f M N hp) |>.trans
      (Iso.homCongr
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
          (ModuleCat.of R R)) (Iso.refl N)) |>.trans
      ModuleCat.homEquiv |>.trans (LinearMap.ringLmapEquivSelf R R N).toEquiv
    have he (g : H Z →ₗ[R] N) : eqv g = g (iteratedPDH0Unit R f d 1) := by
      simp only [eqv, Equiv.trans_apply, completionH0HomEquiv_apply,
        Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
      simp only [iteratedPDH0Unit, Functor.map_comp]
      rfl
    have hf : (eqv : _ → _) = (fun g => g (iteratedPDH0Unit R f d 1)) := funext he
    rw [← hf]
    exact eqv.bijective

variable (p : ℕ) (hp : f = (p : R))
include hp

/-- 二つの実H0反射の間には、元の線形標準単位を保つ同型がある。 -/
theorem exists_iteratedPDH0LinearEquiv :
    ∃ e : H Z ≃ₗ[R] PDCompletionH0 R p d,
      ∀ x : R, e (iteratedPDH0Unit R f d x) =
        pairCompletionH0Unit R (p : R) d x := by
  let B := ModuleCat.of R (PDCompletionH0 R p d)
  let u := pairCompletionH0Unit R (p : R) d
  let v := iteratedPDH0Unit R f d
  let h := iteratedPDH0_isCompleteModuleReflection R f d
  have hB : IsCompleteModuleReflection R (pairKoszulCoordinates R f d) B (u 1) := by
    rw [hp]
    exact pairCompletionH0_isCompleteModuleReflection R (p : R) d
  obtain ⟨f, hf⟩ := (h.universal B hB.isComplete).surjective (u 1)
  obtain ⟨g, hg⟩ := (hB.universal (H Z) h.isComplete).surjective (v 1)
  change f (v 1) = u 1 at hf
  change g (u 1) = v 1 at hg
  have hgf : g.comp f = LinearMap.id := by
    apply (h.universal (H Z) h.isComplete).injective
    change g (f (v 1)) = v 1
    rw [hf, hg]
  have hfg : f.comp g = LinearMap.id := by
    apply (hB.universal B hB.isComplete).injective
    change f (g (u 1)) = u 1
    rw [hg, hf]
  let e : H Z ≃ₗ[R] PDCompletionH0 R p d :=
    { f with
      invFun := g
      left_inv := fun x => LinearMap.congr_fun hgf x
      right_inv := fun x => LinearMap.congr_fun hfg x }
  refine ⟨e, ?_⟩
  intro x
  have hx : v x = x • v 1 := by simpa only [smul_eq_mul, mul_one] using v.map_smul x (1 : R)
  have hu : u x = x • u 1 := by simpa only [smul_eq_mul, mul_one] using u.map_smul x (1 : R)
  change e (v x) = u x
  rw [hx, hu, map_smul]
  exact congrArg (fun t => x • t) hf

/-- 元のRaw線形単位で正規化した、実逐次H0から実PD完備化H0への同型。 -/
def iteratedPDH0LinearEquiv : H Z ≃ₗ[R] PDCompletionH0 R p d :=
  (exists_iteratedPDH0LinearEquiv R f d p hp).choose

/-- 比較は全raw係数の元の完備化像を保つ。 -/
theorem iteratedPDH0LinearEquiv_unit (x : R) :
    iteratedPDH0LinearEquiv R f d p hp (iteratedPDH0Unit R f d x) =
      pairCompletionH0Unit R (p : R) d x :=
  (exists_iteratedPDH0LinearEquiv R f d p hp).choose_spec x

end SerrePositivity.BhattScholze

end IteratedPDH0Reflection

/-! ## 具体的根添加逐次対象のp方向・d方向の導来完備性 -/

@[expose] public noncomputable section DeltaRootSourceIteratedCompletionComplete

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 実p完備化後に実d完備化を施した具体的根添加対象は、なおp導来完備。 -/
theorem deltaRootSourceIteratedPDCompletion_isComplete_p :
    DerivedCompletion.IsComplete A (p : A)
      (DeltaRootSourceIteratedPDCompletion D d b).obj := by
  let X := DeltaRootSourceCoefficientObject d D b
  let Y := (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj X
  have hY : DerivedCompletion.IsComplete A (p : A) Y.obj :=
    DerivedCompletion.derivedComplexCompletionFunctor_isComplete A (p : A) X.obj
  let K := DerivedCategory.Q.objPreimage Y.obj
  let eK : DerivedCategory.Q.obj K ≅ Y.obj := DerivedCategory.Q.objObjPreimageIso Y.obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm hY
  have hstage (n : ℕ) : DerivedCompletion.IsComplete A (p : A)
      (DerivedCategory.Q.obj (DerivedCompletion.complexPowerKoszulStage A d K n)) :=
    DerivedCompletion.isComplete_Q_mappingCone A (p : A)
      (smulId (d ^ n) K) hK hK
  have hC : DerivedCompletion.IsComplete A (p : A)
      (DerivedCompletion.complexCompletionObject A d K) :=
    DerivedCompletion.isComplete_complexTowerHomotopyLimitObject_of_stages A (p : A)
      (DerivedCompletion.complexPowerKoszulStage A d K)
      (DerivedCompletion.complexPowerKoszulTransition A d K) hstage
  let e : DerivedCompletion.complexCompletionObject A d K ≅
      (DeltaRootSourceIteratedPDCompletion D d b).obj :=
    (DerivedCompletion.derivedComplexCompletionComparison A d).symm.app K ≪≫
      (DerivedCompletion.derivedComplexCompletionFunctor A d).mapIso eK
  exact DerivedCompletion.isComplete_of_iso A (p : A) e hC

/-- 同じ具体的逐次対象は、最後の主元完備化によりd導来完備。 -/
theorem deltaRootSourceIteratedPDCompletion_isComplete_d :
    DerivedCompletion.IsComplete A d
      (DeltaRootSourceIteratedPDCompletion D d b).obj :=
  DerivedCompletion.derivedComplexCompletionFunctor_isComplete A d
    ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
      (DeltaRootSourceCoefficientObject d D b)).obj

end SerrePositivity.BhattScholze

end DeltaRootSourceIteratedCompletionComplete
