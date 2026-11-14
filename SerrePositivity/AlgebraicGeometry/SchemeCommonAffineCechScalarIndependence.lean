module

public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechScalarHomology

/-!
概要：共通アフィン細分による Čech H の比較が、共通細分の選択に依存しないことを示す。
方針：二つの共通細分の有限共通被覆へさらに細分し、添字選択の独立性を使う。
規約：比較に用いる同型はすべて実際の細分写像から得る。
使われ方：被覆の取り方に依存しない、射影 Čech H の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable {R : Type u} [CommRing R] (φ : R →+* Γ(Y, ⊤))
variable (M : Y.Modules) [M.IsQuasicoherent]
variable {ι κ ν μ : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ]
variable [Fintype ν] [Fintype μ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens) (W : ν → Y.Opens) (L : μ → Y.Opens)
variable (ρ : ν → ι) (hρ : ∀ j, W j ≤ U (ρ j))
variable (σ : ν → κ) (hσ : ∀ j, W j ≤ V (σ j))
variable (ρ' : μ → ι) (hρ' : ∀ j, L j ≤ U (ρ' j))
variable (σ' : μ → κ) (hσ' : ∀ j, L j ≤ V (σ' j))
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hW : ∀ j, IsAffineOpen (W j)) (hL : ∀ j, IsAffineOpen (L j))
variable (hcW : (⨆ j, W j) = ⊤) (hcL : (⨆ j, L j) = ⊤)

include hU hV hW hL hcW hcL in
/-- 実際の準連接係数の二つの共通アフィン細分による Čech H の比較は同じ。 -/
theorem schemeModuleCechScalarComparison_commonRefinement_independent (q : ℕ)
    [IsIso (openCoverCechRefinementH (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) V W σ hσ q)]
    [IsIso (openCoverCechRefinementH (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U L ρ' hρ' q)]
    [IsIso (openCoverCechRefinementH (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) V L σ' hσ' q)] :
    openCoverCechComparisonIso (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U V W ρ hρ σ hσ q =
      openCoverCechComparisonIso (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U V L ρ' hρ' σ' hσ' q := by
  let P := schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ
  let Z := schemeFiniteCommonOpenCover W L
  let τ := schemeFiniteCommonCoverLeft (ι := ν) (κ := μ)
  let τ' := schemeFiniteCommonCoverRight (ι := ν) (κ := μ)
  have hτ : ∀ j, Z j ≤ W (τ j) := schemeFiniteCommonOpenCover_le_left W L
  have hτ' : ∀ j, Z j ≤ L (τ' j) := schemeFiniteCommonOpenCover_le_right W L
  have hZ : ∀ j, IsAffineOpen (Z j) := schemeFiniteCommonOpenCover_isAffineOpen W L hW hL
  have hcZ : (⨆ j, Z j) = ⊤ := schemeFiniteCommonOpenCover_iSup W L hcW hcL
  haveI : IsIso (openCoverCechRefinementH P W Z (τ) (hτ) q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M W Z (τ) (hτ) hW hZ hcZ q
  haveI : IsIso (openCoverCechRefinementH P L Z (τ') (hτ') q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M L Z (τ') (hτ') hL hZ hcZ q
  haveI : IsIso (openCoverCechRefinementH P U Z (ρ ∘ τ) (fun j ↦ (hτ j).trans (hρ (τ j))) q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M U Z (ρ ∘ τ) (fun j ↦ (hτ j).trans (hρ (τ j))) hU hZ hcZ q
  haveI : IsIso (openCoverCechRefinementH P V Z (σ ∘ τ) (fun j ↦ (hτ j).trans (hσ (τ j))) q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M V Z (σ ∘ τ) (fun j ↦ (hτ j).trans (hσ (τ j))) hV hZ hcZ q
  haveI : IsIso (openCoverCechRefinementH P U Z (ρ' ∘ τ') (fun j ↦ (hτ' j).trans (hρ' (τ' j))) q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M U Z (ρ' ∘ τ') (fun j ↦ (hτ' j).trans (hρ' (τ' j))) hU hZ hcZ q
  haveI : IsIso (openCoverCechRefinementH P V Z (σ' ∘ τ') (fun j ↦ (hτ' j).trans (hσ' (τ' j))) q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M V Z (σ' ∘ τ') (fun j ↦ (hτ' j).trans (hσ' (τ' j))) hV hZ hcZ q
  calc
    _ = openCoverCechComparisonIso P U V Z (ρ ∘ τ)
        (fun j ↦ (hτ j).trans (hρ (τ j))) (σ ∘ τ)
        (fun j ↦ (hτ j).trans (hσ (τ j))) q :=
      (openCoverCechComparisonIso_refine P U V W ρ hρ σ hσ Z τ hτ q).symm
    _ = openCoverCechComparisonIso P U V Z (ρ' ∘ τ')
        (fun j ↦ (hτ' j).trans (hρ' (τ' j))) (σ' ∘ τ')
        (fun j ↦ (hτ' j).trans (hσ' (τ' j))) q :=
      openCoverCechComparisonIso_choice P U V Z _ _ _ _ _ _ _ _ q
    _ = _ := openCoverCechComparisonIso_refine P U V L ρ' hρ' σ' hσ' Z τ' hτ' q

end SerrePositivity.AlgebraicGeometry
