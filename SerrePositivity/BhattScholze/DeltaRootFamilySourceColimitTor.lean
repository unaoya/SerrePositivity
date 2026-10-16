module

public import SerrePositivity.BhattScholze.DeltaDivisionFamilySourceEvaluationColimit
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-! # G7による有限根族の全源評価環への実残余Tor消滅の移送 -/

@[expose] public noncomputable section
universe u
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
  let : PreservesColimitsOfShape ℕ ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1)) :=
    torAlg_preservesSequentialColimits (R := P₀) (S := T) φ (i + 1)
  let H := (ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1)
  have hz : IsZero (colimit (F₀ ⋙ H)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro N
    have hN : IsZero ((F₀ ⋙ H).obj N) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      exact hfin N
    exact hN.eq_of_src _ _
  let e : H.obj (ModuleCat.of P₀ A) ≅ colimit (F₀ ⋙ H) :=
    H.mapIso (deltaDivisionEvaluationSourceFamilyColimitEvalIso D a s).symm ≪≫
      preservesColimitIso H F₀
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
