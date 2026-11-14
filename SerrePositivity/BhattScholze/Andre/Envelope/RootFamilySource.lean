module

public import SerrePositivity.BhattScholze.Andre.Envelope.FamilyEvaluation
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Andre.Envelope.RootFamilyRaw
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion

/-!
# 有限根族の源：導来還元と完全忠実平坦性

## 概要
有限根族の全源評価環への Tor 消滅の移送、導来 β 拡大と raw 残余商、係数側の導来還元、商環上の還元、(p,d) 還元、逐次主元完備化後の還元、ghost 仮定の解消、任意根族の raw p 除算包の p 完全忠実平坦性、完全 prism から源への入力。
BS 著者版 Remark 7.15 の根付き拡大に使う、有限根族の包の係数還元と完全忠実平坦性を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/MonicCandidate`、`Perfection/DeltaAlgebra`。
-/

universe u

/-! ## G7による有限根族の全源評価環への実残余Tor消滅の移送 -/

@[expose] public noncomputable section DeltaRootFamilySourceColimitTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A) {m : ℕ} (s : Fin m ≃ σ)
variable {T : Type u} [CommRing T]
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => deltaDivisionEvaluationSourceFamilyModuleDiagram D a s

/-- G7を実図式へ適用し、有限源商のTor消滅を実β評価環へ移す。 -/
theorem deltaDivisionEvaluationSourceFamily_tor_subsingleton
    (φ : P₀ →+* T) (i : ℕ)
    (hfin : ∀ N : ℕ, Subsingleton (SerrePositivity.TorAlg φ (i + 1)
      (DeltaDivisionEvaluationSourceFamilyQuotient D a s N))) :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    Subsingleton (SerrePositivity.TorAlg φ (i + 1) A) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  let H := (ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1)
  have hz : IsZero (H.obj (colimit F₀)) :=
    torAlg_colimit_isZero_of_stages φ F₀ (i + 1)
      (fun N => ModuleCat.isZero_iff_subsingleton.mpr (hfin N))
  let e : H.obj (ModuleCat.of P₀ A) ≅ H.obj (colimit F₀) :=
    H.mapIso (deltaDivisionEvaluationSourceFamilyColimitEvalIso D a s).symm
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)

variable (d : A)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₁" => RingHom.comp (Ideal.Quotient.mk K₁)
  (deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d))

include s in
/-- 有限根添字について、実残余自由δ射に沿う全β評価環の正次数Torが零。 -/
theorem deltaRootFamilyResidueSource_tor_subsingleton
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E₁ c₁
    Subsingleton (SerrePositivity.TorAlg ψ₁ (i + 1) P₁) := by
  let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
  apply deltaDivisionEvaluationSourceFamily_tor_subsingleton E₁ c₁ s ψ₁ i
  intro N
  exact deltaRootFiniteResidueEvaluationFamilySource_tor_subsingleton D d a s N hpA v hv i

local notation "β₁" => deltaDivisionSourceEval E₁ c₁
local notation "Mψ" => baseChangeScalarModule ψ₁
local notation "Mβ" => baseChangeScalarModule β₁

include s in
/-- Tor対称性で、同じ実残余終域をβに沿って導来拡大するための消滅条件を得る。 -/
theorem deltaRootFamilyResidueSourceEval_torVanishing
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    scalarExtensionTorVanishing β₁ Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
      let : Subsingleton (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        deltaRootFamilyResidueSource_tor_subsingleton
          (D := D) (a := a) (s := s) (d := d) hpA v hv i
      have hz : IsZero (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso ψ₁ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars ψ₁).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso ψ₁ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT

end SerrePositivity.BhattScholze

end DeltaRootFamilySourceColimitTor

/-! ## 有限根族の実導来β拡大と既存raw残余商の標準比較 -/

@[expose] public noncomputable section DeltaRootFamilyResidueSourceDerived

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀

/-- 有限根族について、実残余終域のβ導来拡大は既存raw残余商の次数零対象。 -/
def deltaRootFamilyResidueSourceDerivedIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  letI : Module L₀ Q₀ := Algebra.toModule
  let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₀ Mψ
    (deltaRootFamilyResidueSourceEval_torVanishing
      (D := D) (a := b) (s := s) (d := d) hpA v hv) ≪≫
        boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- 比較同型の順射は、標準導来augmentationと既存残余商比較の合成。 -/
theorem deltaRootFamilyResidueSourceDerivedIso_hom (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    letI : Module L₀ Q₀ := Algebra.toModule
    let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
      (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
    (deltaRootFamilyResidueSourceDerivedIso D d b s hpA v hv).hom.hom =
      (boundedAboveDerivedBaseChangeModuleAugmentation β₀).app Mψ ≫
        (boundedAboveDerivedSingleFunctor.map e.toModuleIso.hom).hom := by
  rfl

end SerrePositivity.BhattScholze

end DeltaRootFamilyResidueSourceDerived

/-! ## 根添加の係数側実導来還元とraw残余商の比較

既存三因子の実導来対象を使い、有限根族の実残余評価比較へ接続する。
導来完備化やperfectionの後の完全忠実平坦性は含まない。
-/

@[expose] public noncomputable section DeltaRootFamilySourceCoefficientResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
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
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)

/-- 有限根族について、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。 -/
def deltaRootFamilySourceCoefficientResidueIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DeltaRootSourceCoefficientReduced D d b ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ (MvPolynomial.C d) c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (deltaRootFamilyResidueSourceDerivedIso D d b s hpA v hv)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。 -/
def deltaRootFamilySourceCoefficientResidueHomologyZeroIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaRootFamilySourceCoefficientResidueIso D d b s hpA v hv))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。 -/
theorem deltaRootFamilySourceCoefficientResidue_homology_isZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootFamilySourceCoefficientResidueIso D d b s hpA v hv)))

end SerrePositivity.BhattScholze

end DeltaRootFamilySourceCoefficientResidue

/-! ## 実商環上の根添加導来還元

(p,d)の通常商への実基底変更を扱う。Koszul還元との同一視や完備化後の
有限根族について、実商係数環上の離散性と元のA/(p,d)上のH0忠実平坦性を証明する。
-/

@[expose] public noncomputable section DeltaRootFamilySourceQuotientFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
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

/-- 実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。 -/
def deltaRootFamilySourceQuotientDerivedRestrictedH0Iso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (DeltaRootSourceQuotientDerived D d b).obj) ≅ MRes :=
  ((derivedRestrictScalarsHomologyIso q₀ 0).app
      (DeltaRootSourceQuotientDerived D d b).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceQuotientDerivedRestrictionIso D d b)) ≪≫
    deltaRootFamilySourceCoefficientResidueHomologyZeroIso
      D d b s hpA v hv

/-- 有限根族について、実商環上の還元そのものの非零次数ホモロジーが消える。 -/
theorem deltaRootFamilySourceQuotientDerived_homology_isZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (DeltaRootSourceQuotientDerived D d b).obj) := by
  have hz := deltaRootFamilySourceCoefficientResidue_homology_isZero
    D d b s hpA v hv i hi
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
def deltaRootFamilySourceQuotientDerivedH0Iso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (DeltaRootSourceQuotientDerived D d b).obj) ≅ ModuleCat.of Q₀ Res₀ := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := deltaRootFamilySourceQuotientDerivedRestrictedH0Iso
    D d b s hpA v hv ≪≫ (deltaRootSourceQuotientResidueRestrictionIso D d b).symm
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

set_option maxHeartbeats 800000 in
-- 実商環上のホモロジーと複数の商作用を同時に照合するため。
/-- 有限根族について、実導来商還元のH0は元のA/(p,d)上忠実平坦。 -/
theorem deltaRootFamilySourceQuotientDerivedH0_faithfullyFlat (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat (A ⧸ k₀)
      ((ModuleCat.restrictScalars (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (DeltaRootSourceQuotientDerived D d b).obj)) := by
  have hpP : Function.Injective (fun x : P₀ => (p : P₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₀)
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
  have hg := witt_ghostMap_injective_of_mul_prime_injective p L₀ hpL
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpP hpL hg v hv
  let H := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
    (DeltaRootSourceQuotientDerived D d b).obj
  let M := (ModuleCat.restrictScalars
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj H
  let eQ := deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv
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

local notation "X₀" => DeltaRootSourceQuotientDerived D d b

/-- 有限根族の実商還元は、標準t構造の非負部分に属する。 -/
theorem deltaRootFamilySourceQuotientDerived_isGE_zero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact deltaRootFamilySourceQuotientDerived_homology_isZero
    D d b s hpA v hv i (by omega)

/-- 同じ入力の下で標準t構造の非正部分にも属する。 -/
theorem deltaRootFamilySourceQuotientDerived_isLE_zero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact deltaRootFamilySourceQuotientDerived_homology_isZero
    D d b s hpA v hv i (by omega)

/-- 実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。 -/
def deltaRootFamilySourceQuotientDerivedSingleIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := deltaRootFamilySourceQuotientDerived_isGE_zero D d b s hpA v hv
  have := deltaRootFamilySourceQuotientDerived_isLE_zero D d b s hpA v hv
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (X₀).obj 0) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv)

/-- この導来同型のH0は、前工程で構成した具体的な商環線形同型そのもの。 -/
theorem deltaRootFamilySourceQuotientDerivedSingleIso_homologyZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
        (deltaRootFamilySourceQuotientDerivedSingleIso
          D d b s hpA v hv).hom.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q₀) 0).hom.app
        (ModuleCat.of Q₀ Res₀) =
      (deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv).hom := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  have := deltaRootFamilySourceQuotientDerived_isGE_zero D d b s hpA v hv
  have := deltaRootFamilySourceQuotientDerived_isLE_zero D d b s hpA v hv
  let e := deltaRootFamilySourceQuotientDerivedH0Iso D d b s hpA v hv
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

end DeltaRootFamilySourceQuotientFlat

/-! ## 元の係数環上の実(p,d)還元とraw残余商

有限根族の実源商での比較を元の係数環へ渡す。一般Koszul還元や完備化後CFFは含まない。
-/

@[expose] public noncomputable section DeltaRootFamilySourcePDResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
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
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)) (DeltaRootSourceCoefficientObject d D b)
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 元のA上の実根添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。 -/
def deltaRootFamilySourceCoefficientPDResidueIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact deltaRootSourceCoefficientPDReductionIso d D b ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (deltaRootFamilySourceQuotientDerivedSingleIso D d b s hpA v hv) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。 -/
def deltaRootFamilySourceCoefficientPDResidueH0Iso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootFamilySourceCoefficientPDResidueIso D d b s hpA v hv)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 元のA上の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem deltaRootFamilySourceCoefficientPDResidue_homology_isZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootFamilySourceCoefficientPDResidueIso D d b s hpA v hv)))

/-- 元のA上の実(p,d)還元のH0は、実係数商A/(p,d)上忠実平坦。 -/
theorem deltaRootFamilySourceCoefficientPDResidueH0_faithfullyFlat (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars κ₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (DeltaRootSourceQuotientDerived D d b).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceCoefficientPDReductionIso d D b)) ≪≫
    (derivedRestrictScalarsHomologyIso κ₀ 0).app (DeltaRootSourceQuotientDerived D d b).obj
  have := deltaRootFamilySourceQuotientDerivedH0_faithfullyFlat
    D d b s hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootFamilySourcePDResidue

/-! ## 実根添加対象の逐次主元完備化後の(p,d)還元

既存の二つの主元完備化を逐次適用した具体的対象を扱う。
原典の(p,d)完備化・環H0候補との比較や離散性は別工程である。
-/

@[expose] public noncomputable section DeltaRootFamilySourceIteratedResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
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
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => DeltaRootSourceCoefficientObject d D b
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 有限根族について、逐次主元完備化後の実還元は標準作用付きraw残余商のsingle対象。 -/
def deltaRootFamilySourceIteratedPDResidueIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b) ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact deltaRootSourceIteratedPDReductionIso D d b hpA hd ≪≫
    deltaRootFamilySourceCoefficientPDResidueIso D d b s hpA v hv

/-- raw比較は合成標準単位の実還元を、未完備対象のraw比較へ送る。 -/
theorem deltaRootFamilySourceIteratedPDResidueIso_unit (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (deltaRootFamilySourceIteratedPDResidueIso D d b s hpA hd v hv).hom =
      (deltaRootFamilySourceCoefficientPDResidueIso D d b s hpA v hv).hom := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  simp only [deltaRootFamilySourceIteratedPDResidueIso, Iso.trans_hom]
  rw [← Category.assoc, deltaRootSourceIteratedPDReductionIso_unit, Category.id_comp]

/-- 逐次主元完備化後の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem deltaRootFamilySourceIteratedPDResidue_homology_isZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b)).obj) :=
  (deltaRootFamilySourceCoefficientPDResidue_homology_isZero
    D d b s hpA v hv i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (deltaRootSourceIteratedPDReductionIso D d b hpA hd)))

/-- 逐次主元完備化後の実(p,d)還元のH0は、標準A/(p,d)上で忠実平坦。 -/
theorem deltaRootFamilySourceIteratedPDResidueH0_faithfullyFlat (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀ ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (DeltaRootSourceIteratedPDCompletion D d b)).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b)).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceIteratedPDReductionIso D d b hpA hd))
  have := deltaRootFamilySourceCoefficientPDResidueH0_faithfullyFlat
    D d b s hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootFamilySourceIteratedResidue

/-! ## 完全prismから有限根族の実逐次完備化源への入力 -/

@[expose] public noncomputable section PerfectPrismRootFamilySourceInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
include hP

private theorem generatorRegular : IsSMulRegular A d := by
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_mul_injective (P.isDistinguished_generator)

include s

/-- 完全prismから、有限根族の実逐次源の実(p,d)還元の非零次数消滅を得る。 -/
theorem perfectPrismRootFamilySource_modPD_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  exact deltaRootFamilySourceIteratedPDResidue_homology_isZero D d b s hP.p_mul_injective
    (generatorRegular P hP) v hv i hi

/-- 同じ実還元のH0は、元のA/(p,d)上で忠実平坦。追加単元・ghost入力は不要。 -/
theorem perfectPrismRootFamilySource_modPDH0_faithfullyFlat :
    Module.FaithfullyFlat Q₀ ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  exact deltaRootFamilySourceIteratedPDResidueH0_faithfullyFlat D d b s hP.p_mul_injective
    (generatorRegular P hP) v hv

/-- 元の同じ実逐次源のp,d完備性と実(p,d)還元の消滅・忠実平坦性を束ねる。 -/
theorem perfectPrismRootFamilySource_complete_residue_inputs :
    DerivedCompletion.IsComplete A (p : A) (X₀).obj ∧
      DerivedCompletion.IsComplete A d (X₀).obj ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj)) ∧
      Module.FaithfullyFlat Q₀
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj) := by
  exact ⟨deltaRootSourceIteratedPDCompletion_isComplete_p D d b,
    deltaRootSourceIteratedPDCompletion_isComplete_d D d b,
    perfectPrismRootFamilySource_modPD_homology_isZero P hP b s,
    perfectPrismRootFamilySource_modPDH0_faithfullyFlat P hP b s⟩

end SerrePositivity.BhattScholze

end PerfectPrismRootFamilySourceInputs

/-! ## G4による任意根族の外部ghost仮定の解消 -/

@[expose] public noncomputable section DeltaRootFamilyRegularGhost

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : P) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qA)
  (CategoryTheory.Functor.obj (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A))
    (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor (ModuleCat.of A B)))

private theorem finiteSourceGhost
    (hpA : Function.Injective (fun z : A => (p : A) * z)) (T : Finset σ) :
    Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T) := by
  apply witt_ghostMap_injective_of_mul_prime_injective
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular A (p : A) from hpA).of_flat
      (S := RelativeFreeDeltaRing (R := P) T)

private theorem nextSourceGhost (T : Finset σ)
    (hpB : Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
      (fun t : T => DeltaStructure.frobeniusLift E (r t)) =>
      (p : DeltaAdjoinDivision E (p : P)
        (fun t : T => DeltaStructure.frobeniusLift E (r t))) * z)) :
    Function.Injective (WittVector.ghostMap : WittVector p
      (RelativeFreeDeltaRing (R := DeltaAdjoinDivision E (p : P)
        (fun t : T => DeltaStructure.frobeniusLift E (r t))) PUnit.{u+1}) → ℕ →
      RelativeFreeDeltaRing (R := DeltaAdjoinDivision E (p : P)
        (fun t : T => DeltaStructure.frobeniusLift E (r t))) PUnit.{u+1}) := by
  let C := DeltaAdjoinDivision E (p : P)
    (fun t : T => DeltaStructure.frobeniusLift E (r t))
  have h := (show IsSMulRegular C (p : C) from hpB).of_flat
    (S := RelativeFreeDeltaRing (R := C) PUnit.{u+1})
  rw [map_natCast (algebraMap C (RelativeFreeDeltaRing (R := C) PUnit.{u+1})) p] at h
  exact witt_ghostMap_injective_of_mul_prime_injective p _ h

/-- 任意根族のraw p除算包のp正則性。外部ghost仮定は不要。 -/
theorem deltaRootFamilyRaw_p_mul_injective_of_p_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    Function.Injective (fun z : B => (p : B) * z) :=
  deltaRootFamilyRaw_p_mul_injective (η := PUnit.{u+1}) D b hpA w hw
    (finiteSourceGhost hpA) (nextSourceGhost D b)

/-- 任意根族の実p完備化の標準mod p還元の非零次数消滅。 -/
theorem deltaRootFamilyCompletedModP_homology_isZero_of_p_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat QA) i).obj (Y).obj) :=
  deltaRootFamilyCompletedModP_homology_isZero (η := PUnit.{u+1}) D b hpA w hw
    (finiteSourceGhost hpA) (nextSourceGhost D b)
    (deltaRootSource_ghostMap_injective (σ := σ) hpA) i hi

/-- 任意根族の実p完備化の標準mod p還元H0は、追加ghost仮定なしに忠実平坦。 -/
theorem deltaRootFamilyCompletedModPH0_faithfullyFlat_of_p_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    Module.FaithfullyFlat QA
      ((DerivedCategory.homologyFunctor (ModuleCat QA) 0).obj (Y).obj) :=
  deltaRootFamilyCompletedModPH0_moduleFaithfullyFlat (η := PUnit.{u+1}) D b hpA w hw
    (finiteSourceGhost hpA) (nextSourceGhost D b)
    (deltaRootSource_ghostMap_injective (σ := σ) hpA)

end SerrePositivity.BhattScholze

end DeltaRootFamilyRegularGhost

/-! ## 任意根族の実raw p除算包のp完全忠実平坦性 -/

@[expose] public noncomputable section DeltaRootFamilyRawCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : P) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I

/-- G4でghost単射を供給した通常剰余テンソルの忠実平坦性。 -/
theorem deltaRootFamilyRaw_residueTensor_faithfullyFlat
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    Module.FaithfullyFlat QA (QA ⊗[A] B) := by
  let hg := deltaRootSource_ghostMap_injective (σ := σ) hpA
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  have := deltaRootRawModP_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw).toLinearEquiv

/-- 実raw包のp正則性を、元のAの標準係数スカラーについて表す。 -/
theorem deltaRootFamilyRaw_p_smul_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    IsSMulRegular B (p : A) := by
  intro x y h
  apply deltaRootFamilyRaw_p_mul_injective_of_p_regular D b hpA w hw
  simp only [Algebra.smul_def, map_natCast] at h
  exact h

/-- 任意根族の実係数射A→Bは、G3によりp完全忠実平坦。 -/
theorem deltaRootFamilyRaw_isCompletelyFaithfullyFlat
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    IsCompletelyFaithfullyFlat I B :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hpA B
    (deltaRootFamilyRaw_p_smul_regular D b hpA w hw)
    (deltaRootFamilyRaw_residueTensor_faithfullyFlat D b hpA w hw)

end SerrePositivity.BhattScholze

end DeltaRootFamilyRawCompletelyFlat
