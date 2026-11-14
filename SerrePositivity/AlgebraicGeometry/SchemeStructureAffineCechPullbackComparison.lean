module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechComparisonNaturality
public import SerrePositivity.AlgebraicGeometry.SchemeCechPullbackComparison
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullbackComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
概要：アフィン射の構造層の引き戻しは、共通アフィン細分の比較と可換。
方針：四つの細分写像の同型性を準連接性から供給し、実際の引き戻しの自然性を使う。
規約：同型性は結論のための追加仮定とせず、アフィン被覆から証明する。
使われ方：閉厚化、アフィン底変換、動く基底の遷移の被覆比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
universe u
variable {X Y : Scheme.{u}}
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable {R : Type u} [CommRing R] (f : X ⟶ Y) [IsAffineHom f]
variable (φY : R →+* Γ(Y, ⊤)) (φX : R →+* Γ(X, ⊤))
variable (hφ : φX = f.appTop.hom.comp φY)
variable {ι κ : Type} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤)

/-- アフィン射の実際の引き戻しは、共通アフィン細分による Čech H の比較と可換。
原典 Stacks 30.2.6 の Hⁱ の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeStructureAffineCechPullback_comparison_naturality (q : ℕ) :
    HomologicalComplex.homologyMap (schemeStructureCechPullbackMap f φY φX hφ U) q ≫
        (schemeModuleCommonAffineCechScalarHomologyIso φX (schemeStructureModule X)
          (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j)
          (fun i ↦ (hU i).preimage f) (fun j ↦ (hV j).preimage f)
          (f.iSup_preimage_eq_top hcU) (f.iSup_preimage_eq_top hcV) q).hom =
      (schemeModuleCommonAffineCechScalarHomologyIso φY (schemeStructureModule Y)
        U V hU hV hcU hcV q).hom ≫
        HomologicalComplex.homologyMap (schemeStructureCechPullbackMap f φY φX hφ V) q := by
  let W := schemeFiniteCommonOpenCover U V
  let ρ := schemeFiniteCommonCoverLeft (ι := ι) (κ := κ)
  let σ := schemeFiniteCommonCoverRight (ι := ι) (κ := κ)
  have hρ : ∀ j, W j ≤ U (ρ j) := schemeFiniteCommonOpenCover_le_left U V
  have hσ : ∀ j, W j ≤ V (σ j) := schemeFiniteCommonOpenCover_le_right U V
  have hW : ∀ j, IsAffineOpen (W j) := schemeFiniteCommonOpenCover_isAffineOpen U V hU hV
  have hcW : (⨆ j, W j) = ⊤ := schemeFiniteCommonOpenCover_iSup U V hcU hcV
  haveI : IsIso (openCoverCechRefinementH
      (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φY) U W ρ hρ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φY (schemeStructureModule Y)
      U W ρ hρ hU hW hcW q
  haveI : IsIso (openCoverCechRefinementH
      (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φY) V W σ hσ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φY (schemeStructureModule Y)
      V W σ hσ hV hW hcW q
  haveI : IsIso (openCoverCechRefinementH
      (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φX)
      (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ W j) ρ
      (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φX (schemeStructureModule X)
      _ _ ρ _ (fun i ↦ (hU i).preimage f) (fun j ↦ (hW j).preimage f)
      (f.iSup_preimage_eq_top hcW) q
  haveI : IsIso (openCoverCechRefinementH
      (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φX)
      (fun i ↦ f ⁻¹ᵁ V i) (fun j ↦ f ⁻¹ᵁ W j) σ
      (fun j ↦ ((Opens.map f.base).map (homOfLE (hσ j))).le) q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φX (schemeStructureModule X)
      _ _ σ _ (fun i ↦ (hV i).preimage f) (fun j ↦ (hW j).preimage f)
      (f.iSup_preimage_eq_top hcW) q
  exact schemeCechPullback_comparison_naturality f _ _
    (schemeStructureCechPullbackCoefficient f φY φX hφ) U V W ρ hρ σ hσ q

end SerrePositivity.AlgebraicGeometry
