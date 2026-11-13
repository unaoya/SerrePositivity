module

public import SerrePositivity.AlgebraicGeometry.SchemeCechPreimage
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechComparison

/-!
概要：共通細分で定める Čech H の比較を、異なるスキーム間の引き戻しに自然にする。
方針：三つの実際の細分の可換な正方形を使い、共通細分への同型を消去する。
規約：引き戻しに平坦性を仮定せず、係数の射を指定する。
使われ方：閉厚化・底変換・有限段の遷移の共通アフィン比較との整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u v
variable {X Y : Scheme.{u}} {R : Type v} [CommRing R]
variable (f : X ⟶ Y) (P : (Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} R)
variable (Q : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R)
variable (η : P ⟶ (Opens.map f.base).op ⋙ Q)
variable {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
variable (U : ι → Y.Opens) (V : κ → Y.Opens) (W : ν → Y.Opens)
variable (ρ : ν → ι) (hρ : ∀ j, W j ≤ U (ρ j))
variable (σ : ν → κ) (hσ : ∀ j, W j ≤ V (σ j))

/-- 共通細分の Čech H の比較は、実際のスキームの引き戻しに自然。 -/
theorem schemeCechPullback_comparison_naturality (q : ℕ)
    [IsIso (openCoverCechRefinementH P U W ρ hρ q)]
    [IsIso (openCoverCechRefinementH P V W σ hσ q)]
    [IsIso (openCoverCechRefinementH Q (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ W j) ρ
      (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) q)]
    [IsIso (openCoverCechRefinementH Q (fun i ↦ f ⁻¹ᵁ V i) (fun j ↦ f ⁻¹ᵁ W j) σ
      (fun j ↦ ((Opens.map f.base).map (homOfLE (hσ j))).le) q)] :
    HomologicalComplex.homologyMap (schemeCechPullbackMap f Q η U) q ≫
        (openCoverCechComparisonIso Q (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j)
          (fun j ↦ f ⁻¹ᵁ W j) ρ
          (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) σ
          (fun j ↦ ((Opens.map f.base).map (homOfLE (hσ j))).le) q).hom =
      (openCoverCechComparisonIso P U V W ρ hρ σ hσ q).hom ≫
        HomologicalComplex.homologyMap (schemeCechPullbackMap f Q η V) q := by
  let a := openCoverCechRefinementH P U W ρ hρ q
  let b := openCoverCechRefinementH P V W σ hσ q
  let c := openCoverCechRefinementH Q (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ W j) ρ
    (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) q
  let d := openCoverCechRefinementH Q (fun i ↦ f ⁻¹ᵁ V i) (fun j ↦ f ⁻¹ᵁ W j) σ
    (fun j ↦ ((Opens.map f.base).map (homOfLE (hσ j))).le) q
  let u := HomologicalComplex.homologyMap (schemeCechPullbackMap f Q η U) q
  let v := HomologicalComplex.homologyMap (schemeCechPullbackMap f Q η V) q
  let w := HomologicalComplex.homologyMap (schemeCechPullbackMap f Q η W) q
  have hu : a ≫ w = u ≫ c := schemeCechPullback_homology_refinement f Q η U W ρ hρ q
  have hv : b ≫ w = v ≫ d := schemeCechPullback_homology_refinement f Q η V W σ hσ q
  change u ≫ (c ≫ inv d) = (a ≫ inv b) ≫ v
  apply (cancel_mono d).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hv]
  simp only [IsIso.inv_hom_id_assoc]
  exact hu.symm

end SerrePositivity.AlgebraicGeometry
