module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementNaturality

/-!
概要：共通細分への二つの Čech H の同型から、被覆間の比較を作る。
方針：一方の細分写像と他方の逆を合成し、共通細分で自然性を検査する。
規約：同型性は実際の細分写像について与え、比較の写像を別に選ばない。
使われ方：共通アフィン細分による自然な被覆間の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R)

/-- 実際の細分写像が誘導する Čech H の射。 -/
abbrev openCoverCechRefinementH (U : ι → Opens X) (V : κ → Opens X)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) (q : ℕ) :=
  HomologicalComplex.homologyMap (openCoverCechRefinementMap P U V ρ hρ) q

/-- 係数前層の射が誘導する Čech H の射。 -/
abbrev openCoverCechCoefficientH {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R}
    (η : P ⟶ Q) (U : ι → Opens X) (q : ℕ) :=
  HomologicalComplex.homologyMap (fullCechComplexMap (openCoverCechCoefficientMap η U)) q

variable (U : ι → Opens X) (V : κ → Opens X) (W : ν → Opens X)
variable (ρ : ν → ι) (hρ : ∀ j, W j ≤ U (ρ j))
variable (σ : ν → κ) (hσ : ∀ j, W j ≤ V (σ j))

/-- 共通細分を用いる、二つの被覆の Čech H の比較。 -/
def openCoverCechComparisonIso (q : ℕ)
    [IsIso (openCoverCechRefinementH P U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH P V W σ hσ q)] :
    (fullCechComplex (openCoverCechDiagram P U)).homology q ≅
      (fullCechComplex (openCoverCechDiagram P V)).homology q :=
  asIso (openCoverCechRefinementH P U W ρ hρ q) ≪≫
    (asIso (openCoverCechRefinementH P V W σ hσ q)).symm

/-- 共通細分による Čech H の比較は係数前層の射に自然。 -/
theorem openCoverCechComparisonIso_naturality
    {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R} (η : P ⟶ Q) (q : ℕ)
    [IsIso (openCoverCechRefinementH P U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH P V W σ hσ q)]
    [IsIso (openCoverCechRefinementH Q U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH Q V W σ hσ q)] :
    openCoverCechCoefficientH P η U q ≫
        (openCoverCechComparisonIso Q U V W ρ hρ σ hσ q).hom =
      (openCoverCechComparisonIso P U V W ρ hρ σ hσ q).hom ≫
        openCoverCechCoefficientH P η V q := by
  let a := openCoverCechRefinementH P U W ρ hρ q
  let b := openCoverCechRefinementH P V W σ hσ q
  let c := openCoverCechRefinementH Q U W ρ hρ q
  let d := openCoverCechRefinementH Q V W σ hσ q
  let u := openCoverCechCoefficientH P η U q
  let v := openCoverCechCoefficientH P η V q
  let w := openCoverCechCoefficientH P η W q
  have hu : a ≫ w = u ≫ c := openCoverCechRefinement_homology_naturality U W ρ hρ η q
  have hv : b ≫ w = v ≫ d := openCoverCechRefinement_homology_naturality V W σ hσ η q
  change u ≫ (c ≫ inv d) = (a ≫ inv b) ≫ v
  apply (cancel_mono d).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hv]
  simp only [IsIso.inv_hom_id_assoc]
  exact hu.symm

/-- 細分写像の選択を変えても、誘導される Čech H の射は同じ。 -/
theorem openCoverCechRefinementH_eq (ρ' : ν → ι)
    (hρ' : ∀ j, W j ≤ U (ρ' j)) (q : ℕ) :
    openCoverCechRefinementH P U W ρ hρ q =
      openCoverCechRefinementH P U W ρ' hρ' q :=
  openCoverCechRefinement_homologyMap_eq P U W ρ ρ' hρ hρ' q

/-- 同じ共通細分への添字の選択によらず、被覆間の Čech H の比較は同じ。 -/
theorem openCoverCechComparisonIso_choice
    (ρ' : ν → ι) (hρ' : ∀ j, W j ≤ U (ρ' j))
    (σ' : ν → κ) (hσ' : ∀ j, W j ≤ V (σ' j)) (q : ℕ)
    [IsIso (openCoverCechRefinementH P U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH P V W σ hσ q)]
    [IsIso (openCoverCechRefinementH P U W ρ' hρ' q)]
    [IsIso (openCoverCechRefinementH P V W σ' hσ' q)] :
    openCoverCechComparisonIso P U V W ρ hρ σ hσ q =
      openCoverCechComparisonIso P U V W ρ' hρ' σ' hσ' q := by
  apply Iso.ext
  change openCoverCechRefinementH P U W ρ hρ q ≫
      inv (openCoverCechRefinementH P V W σ hσ q) =
    openCoverCechRefinementH P U W ρ' hρ' q ≫
      inv (openCoverCechRefinementH P V W σ' hσ' q)
  have ha := openCoverCechRefinementH_eq P U W ρ hρ ρ' hρ' q
  have hb := openCoverCechRefinementH_eq P V W σ hσ σ' hσ' q
  apply (cancel_mono (openCoverCechRefinementH P V W σ' hσ' q)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hb]
  simp only [IsIso.inv_hom_id, Category.comp_id]
  exact ha

/-- 共通細分をさらに細分しても、Čech H の被覆間の比較は変わらない。 -/
theorem openCoverCechComparisonIso_refine
    {μ : Type} [LinearOrder μ] (Z : μ → Opens X)
    (τ : μ → ν) (hτ : ∀ j, Z j ≤ W (τ j)) (q : ℕ)
    [IsIso (openCoverCechRefinementH P U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH P V W σ hσ q)]
    [IsIso (openCoverCechRefinementH P W Z τ hτ q)]
    [IsIso (openCoverCechRefinementH P U Z (ρ ∘ τ)
      (fun j ↦ (hτ j).trans (hρ (τ j))) q)]
    [IsIso (openCoverCechRefinementH P V Z (σ ∘ τ)
      (fun j ↦ (hτ j).trans (hσ (τ j))) q)] :
    openCoverCechComparisonIso P U V Z (ρ ∘ τ)
        (fun j ↦ (hτ j).trans (hρ (τ j))) (σ ∘ τ)
        (fun j ↦ (hτ j).trans (hσ (τ j))) q =
      openCoverCechComparisonIso P U V W ρ hρ σ hσ q := by
  let a := openCoverCechRefinementH P U W ρ hρ q
  let b := openCoverCechRefinementH P V W σ hσ q
  let c := openCoverCechRefinementH P W Z τ hτ q
  let d := openCoverCechRefinementH P U Z (ρ ∘ τ)
    (fun j ↦ (hτ j).trans (hρ (τ j))) q
  let e := openCoverCechRefinementH P V Z (σ ∘ τ)
    (fun j ↦ (hτ j).trans (hσ (τ j))) q
  have hd : a ≫ c = d := by
    simpa only [HomologicalComplex.homologyMap_comp] using congrArg
      (fun f ↦ HomologicalComplex.homologyMap f q)
      (openCoverCechRefinementMap_comp U W ρ hρ Z τ hτ (P := P))
  have he : b ≫ c = e := by
    simpa only [HomologicalComplex.homologyMap_comp] using congrArg
      (fun f ↦ HomologicalComplex.homologyMap f q)
      (openCoverCechRefinementMap_comp V W σ hσ Z τ hτ (P := P))
  apply Iso.ext
  change d ≫ inv e = a ≫ inv b
  apply (cancel_mono e).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← he]
  simp only [IsIso.inv_hom_id_assoc]
  exact hd.symm

/-- 一つの共通細分で作る三つの Čech H の比較は合成に整合する。 -/
theorem openCoverCechComparisonIso_trans
    {μ : Type} [LinearOrder μ] (T : μ → Opens X)
    (τ : ν → μ) (hτ : ∀ j, W j ≤ T (τ j)) (q : ℕ)
    [IsIso (openCoverCechRefinementH P U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH P V W σ hσ q)]
    [IsIso (openCoverCechRefinementH P T W τ hτ q)] :
    openCoverCechComparisonIso P U V W ρ hρ σ hσ q ≪≫
        openCoverCechComparisonIso P V T W σ hσ τ hτ q =
      openCoverCechComparisonIso P U T W ρ hρ τ hτ q := by
  apply Iso.ext
  change (openCoverCechRefinementH P U W ρ hρ q ≫
      inv (openCoverCechRefinementH P V W σ hσ q)) ≫
      (openCoverCechRefinementH P V W σ hσ q ≫
        inv (openCoverCechRefinementH P T W τ hτ q)) =
    openCoverCechRefinementH P U W ρ hρ q ≫ inv (openCoverCechRefinementH P T W τ hτ q)
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

end SerrePositivity.AlgebraicGeometry
