module

public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechScalarHomology
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechFrobenius

/-!
概要：構造層の被覆によらない Čech H の比較は、スカラーをねじる係数の射に自然。
方針：有限共通アフィン細分で、両方のスカラー作用の細分写像が同型であることを使う。
規約：自然性の結論に細分の同型性を仮定として足さない。
使われ方：Frobenius を含めた五つの比較を、同じ実際の構造層の写像で照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Y : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable {R : Type u} [CommRing R] (φ ψ : R →+* Γ(Y, ⊤))
variable {ι κ : Type} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤)

/-- 二つのスカラー作用の間の実際の係数の射に対する、被覆比較の自然性。
原典 Stacks 30.2.6 の被覆の比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeStructureCommonAffineCechCoefficient_naturality
    (η : schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φ ⟶
      schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars ψ) (q : ℕ) :
    openCoverCechCoefficientH _ η U q ≫
        (schemeModuleCommonAffineCechScalarHomologyIso ψ (schemeStructureModule Y)
          U V hU hV hcU hcV q).hom =
      (schemeModuleCommonAffineCechScalarHomologyIso φ (schemeStructureModule Y)
        U V hU hV hcU hcV q).hom ≫ openCoverCechCoefficientH _ η V q := by
  let W := schemeFiniteCommonOpenCover U V
  let ρ := schemeFiniteCommonCoverLeft (ι := ι) (κ := κ)
  let σ := schemeFiniteCommonCoverRight (ι := ι) (κ := κ)
  have hρ : ∀ j, W j ≤ U (ρ j) := schemeFiniteCommonOpenCover_le_left U V
  have hσ : ∀ j, W j ≤ V (σ j) := schemeFiniteCommonOpenCover_le_right U V
  have hW : ∀ j, IsAffineOpen (W j) := schemeFiniteCommonOpenCover_isAffineOpen U V hU hV
  have hcW : (⨆ j, W j) = ⊤ := schemeFiniteCommonOpenCover_iSup U V hcU hcV
  haveI : IsIso (openCoverCechRefinementH (schemeStructureCechPresheaf Y ⋙
      ModuleCat.restrictScalars φ) U W ρ hρ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ (schemeStructureModule Y)
      U W ρ hρ hU hW hcW q
  haveI : IsIso (openCoverCechRefinementH (schemeStructureCechPresheaf Y ⋙
      ModuleCat.restrictScalars φ) V W σ hσ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ (schemeStructureModule Y)
      V W σ hσ hV hW hcW q
  haveI : IsIso (openCoverCechRefinementH (schemeStructureCechPresheaf Y ⋙
      ModuleCat.restrictScalars ψ) U W ρ hρ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso ψ (schemeStructureModule Y)
      U W ρ hρ hU hW hcW q
  haveI : IsIso (openCoverCechRefinementH (schemeStructureCechPresheaf Y ⋙
      ModuleCat.restrictScalars ψ) V W σ hσ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso ψ (schemeStructureModule Y)
      V W σ hσ hV hW hcW q
  exact openCoverCechComparisonIso_naturality _ U V W ρ hρ σ hσ η q

/-- 実際の構造層の Frobenius は、共通アフィン細分による被覆比較と可換。
原典 BST13 Lemma 3.9(1) と Stacks 30.2.6 の Hⁱ の比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeStructureCommonAffineCechFrobenius_naturality
    (p : ℕ) (hp : p.Prime) [ExpChar R p] (hz : (p : R) = 0) (q : ℕ) :
    openCoverCechCoefficientH _ (schemeStructureCechFrobeniusCoefficient Y φ p hp hz) U q ≫
        (schemeModuleCommonAffineCechScalarHomologyIso (φ.comp (frobenius R p))
          (schemeStructureModule Y) U V hU hV hcU hcV q).hom =
      (schemeModuleCommonAffineCechScalarHomologyIso φ (schemeStructureModule Y)
        U V hU hV hcU hcV q).hom ≫
          openCoverCechCoefficientH _ (schemeStructureCechFrobeniusCoefficient Y φ p hp hz) V q :=
  schemeStructureCommonAffineCechCoefficient_naturality φ (φ.comp (frobenius R p))
    U V hU hV hcU hcV (schemeStructureCechFrobeniusCoefficient Y φ p hp hz) q

end SerrePositivity.AlgebraicGeometry
