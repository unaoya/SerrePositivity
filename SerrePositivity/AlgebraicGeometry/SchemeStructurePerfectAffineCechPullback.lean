module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback
public import SerrePositivity.AlgebraicGeometry.SchemeCechPullbackComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
概要：実際の環の Frobenius 順極限後も、アフィン射の引き戻しは共通細分の比較と可換。
方針：四つの細分写像の同型性を準連接性から供給し、実際の引き戻しの自然性を使う。
規約：同型性は結論のための追加仮定とせず、アフィン被覆から証明する。
使われ方：閉厚化、アフィン底変換、動く基底の遷移の被覆比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
universe u
/-- 2e のアフィン比較から供給した、Frobenius 後の実際の細分射の同型性。 -/
private theorem perfectAffineRefinementIsIso (Z : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from Z))]
    (p : ℕ) (hp : p.Prime) (hZ : ∀ O, (p : Z.presheaf.obj O) = 0)
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
    (U : ι → Z.Opens) (V : κ → Z.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j)) (hU : ∀ i, IsAffineOpen (U i))
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤) (q : ℕ) :
    IsIso (openCoverCechRefinementH (frobeniusRingDiagram Z.presheaf p hp hZ)
      U V ρ hρ q) :=
  (quasiIsoAt_iff_isIso_homologyMap _ q).mp
    (schemeStructureFrobeniusCechRefinement_quasiIsoAt Z p hp hZ U V ρ hρ hU hV hcV q)

variable {X Y : Scheme.{u}}
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable (f : X ⟶ Y) [IsAffineHom f]
variable (p : ℕ) (hp : p.Prime)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable (hX : ∀ O, (p : X.presheaf.obj O) = 0)
variable {ι κ : Type} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤)

/-- Frobenius 順極限後のアフィン射の実際の引き戻しは、共通アフィン細分の比較と可換。
原典 Stacks 30.2.6 の Hⁱ の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeStructurePerfectAffineCechPullback_comparison_naturality (q : ℕ) :
    HomologicalComplex.homologyMap (schemeStructurePerfectCechPullbackMap f p hp hY hX U) q ≫
        (schemeStructurePerfectCommonAffineCechHomologyIso X p hp hX
          (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j)
          (fun i ↦ (hU i).preimage f) (fun j ↦ (hV j).preimage f)
          (f.iSup_preimage_eq_top hcU) (f.iSup_preimage_eq_top hcV) q).hom =
      (schemeStructurePerfectCommonAffineCechHomologyIso Y p hp hY
        U V hU hV hcU hcV q).hom ≫
        HomologicalComplex.homologyMap (schemeStructurePerfectCechPullbackMap f p hp hY hX V) q := by
  let W := schemeFiniteCommonOpenCover U V
  let ρ := schemeFiniteCommonCoverLeft (ι := ι) (κ := κ)
  let σ := schemeFiniteCommonCoverRight (ι := ι) (κ := κ)
  have hρ : ∀ j, W j ≤ U (ρ j) := schemeFiniteCommonOpenCover_le_left U V
  have hσ : ∀ j, W j ≤ V (σ j) := schemeFiniteCommonOpenCover_le_right U V
  have hW : ∀ j, IsAffineOpen (W j) := schemeFiniteCommonOpenCover_isAffineOpen U V hU hV
  have hcW : (⨆ j, W j) = ⊤ := schemeFiniteCommonOpenCover_iSup U V hcU hcV
  haveI : IsIso (openCoverCechRefinementH
      (frobeniusRingDiagram Y.presheaf p hp hY) U W ρ hρ q) :=
    perfectAffineRefinementIsIso Y p hp hY
      U W ρ hρ hU hW hcW q
  haveI : IsIso (openCoverCechRefinementH
      (frobeniusRingDiagram Y.presheaf p hp hY) V W σ hσ q) :=
    perfectAffineRefinementIsIso Y p hp hY
      V W σ hσ hV hW hcW q
  haveI : IsIso (openCoverCechRefinementH
      (frobeniusRingDiagram X.presheaf p hp hX)
      (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ W j) ρ
      (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) q) :=
    perfectAffineRefinementIsIso X p hp hX
      _ _ ρ _ (fun i ↦ (hU i).preimage f) (fun j ↦ (hW j).preimage f)
      (f.iSup_preimage_eq_top hcW) q
  haveI : IsIso (openCoverCechRefinementH
      (frobeniusRingDiagram X.presheaf p hp hX)
      (fun i ↦ f ⁻¹ᵁ V i) (fun j ↦ f ⁻¹ᵁ W j) σ
      (fun j ↦ ((Opens.map f.base).map (homOfLE (hσ j))).le) q) :=
    perfectAffineRefinementIsIso X p hp hX
      _ _ σ _ (fun i ↦ (hV i).preimage f) (fun j ↦ (hW j).preimage f)
      (f.iSup_preimage_eq_top hcW) q
  exact schemeCechPullback_comparison_naturality f _ _
    (schemeStructurePerfectPullbackCoefficient f p hp hY hX) U V W ρ hρ σ hσ q

end SerrePositivity.AlgebraicGeometry
