module

public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootBoundedSupportResidueDerived

/-! # 任意根族の標準図式に対する無条件のTor交換 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q" => L ⧸ I
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "β" => deltaDivisionSourceEval E r
local notation "Mψ" => baseChangeScalarModule ψ
local notation "Mβ" => baseChangeScalarModule β
local notation "F" => deltaDivisionBoundedSupportModuleDiagram E r
local notation "Res" => DeltaAdjoinDivisionResidue E (MvPolynomial.C d) r
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β) (ModuleCat.of P Res)

/-- 共通G7-Finsetを元の有界深さ図式へ適用したTor交換。 -/
theorem deltaRootBoundedSupport_preservesColimit :
    ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)) := by
  intro i
  let := torAlg_preservesFinsetColimits (σ × ℕ) ψ (i + 1)
  infer_instance

/-- 任意根族の全評価源の正次数Tor消滅。余極限交換の追加仮定は不要。 -/
theorem deltaRootEvaluation_tor_subsingleton
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  exact deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    D d b hpA v hv i (deltaRootBoundedSupport_preservesColimit D d b i)

/-- 元の実β評価の高次Tor消滅を、具体的係数加群とともに供給する。 -/
theorem deltaRootBoundedSupportResidueEval_torVanishing_unconditional
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    scalarExtensionTorVanishing β Mψ := by
  exact deltaRootBoundedSupportResidueEval_torVanishing D d b hpA v hv
    (deltaRootBoundedSupport_preservesColimit D d b)

end SerrePositivity.BhattScholze
