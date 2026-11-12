module

public import SerrePositivity.AlgebraicGeometry.SchemeModuleCechScalarRefinement
public import SerrePositivity.AlgebraicGeometry.SchemeFiniteCommonCover
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechComparison

/-!
概要：二つの有限アフィン被覆で計算した、準連接層の Čech H を比較する。
方針：実際の有限共通アフィン被覆を取り、二つの細分写像の同型を使う。
規約：次数 q の H は全タプルの Čech 複体の H である。
使われ方：射影標準開での計算を、被覆によらない比較にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable {R : Type u} [CommRing R] (φ : R →+* Γ(Y, ⊤))
variable (M : Y.Modules) [M.IsQuasicoherent]
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤)

/-- 二つの有限アフィン被覆による、準連接層の Čech H の比較同型。
原典 Stacks 30.2.6 のアフィン被覆の比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def schemeModuleCommonAffineCechScalarHomologyIso (q : ℕ) :
    (fullCechComplex (openCoverCechDiagram (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U)).homology q ≅
      (fullCechComplex (openCoverCechDiagram (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) V)).homology q := by
  let W := schemeFiniteCommonOpenCover U V
  let ρ := schemeFiniteCommonCoverLeft (ι := ι) (κ := κ)
  let σ := schemeFiniteCommonCoverRight (ι := ι) (κ := κ)
  have hρ : ∀ j, W j ≤ U (ρ j) := schemeFiniteCommonOpenCover_le_left U V
  have hσ : ∀ j, W j ≤ V (σ j) := schemeFiniteCommonOpenCover_le_right U V
  have hW : ∀ j, IsAffineOpen (W j) := schemeFiniteCommonOpenCover_isAffineOpen U V hU hV
  have hcW : (⨆ j, W j) = ⊤ := schemeFiniteCommonOpenCover_iSup U V hcU hcV
  haveI : IsIso (openCoverCechRefinementH (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U W ρ hρ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M U W ρ hρ hU hW hcW q
  haveI : IsIso (openCoverCechRefinementH (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) V W σ hσ q) :=
    schemeModuleCechScalarRefinement_homologyMap_isIso φ M V W σ hσ hV hW hcW q
  exact openCoverCechComparisonIso (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U V W ρ hρ σ hσ q

end SerrePositivity.AlgebraicGeometry
