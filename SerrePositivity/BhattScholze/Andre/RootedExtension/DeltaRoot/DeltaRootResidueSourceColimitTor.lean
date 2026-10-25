module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionSourceEvaluationColimitTor
public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootFiniteResidueSourceTor

/-! # G7交換入力に相対的な根添加の実残余全源Tor

任意有限δ深さで証明した消滅を、実評価環へ移す。
G7の交換入力を保持し、実導来完備化後CFFや一般B4全射性は結論しない。
-/

@[expose] public noncomputable section
universe u
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
