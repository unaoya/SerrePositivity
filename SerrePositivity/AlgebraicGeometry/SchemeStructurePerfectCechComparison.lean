module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureIntCechRefinement
public import SerrePositivity.AlgebraicGeometry.SchemeFiniteCommonCover
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechComparison

/-!
概要：実際の構造層の Frobenius 順極限の Čech H を、有限共通アフィン細分で比較する。
方針：2e の同じ共通被覆と比較を使い、細分の同型性を前の補題から供給する。
規約：導来関手のコホモロジーを定義し直さず、Čech 版のまま述べる。
使われ方：F8 の実際の環の係数で計算する Čech H の被覆によらない比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable (Y : Scheme.{u}) [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable (p : ℕ) (hp : p.Prime) (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable {ι κ : Type} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤)

/-- 実際の構造層の Frobenius 順極限についての、二つの有限アフィン被覆の Čech H の比較。
Stacks 30.2.6 の被覆比較と BST13 Lemma 3.9 の極限に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def schemeStructurePerfectCommonAffineCechHomologyIso (q : ℕ) :
    (fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U)).homology q ≅
      (fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) V)).homology q := by
  let P := frobeniusRingDiagram Y.presheaf p hp hY
  let W := schemeFiniteCommonOpenCover U V
  let ρ := schemeFiniteCommonCoverLeft (ι := ι) (κ := κ)
  let σ := schemeFiniteCommonCoverRight (ι := ι) (κ := κ)
  have hρ : ∀ j, W j ≤ U (ρ j) := schemeFiniteCommonOpenCover_le_left U V
  have hσ : ∀ j, W j ≤ V (σ j) := schemeFiniteCommonOpenCover_le_right U V
  have hW : ∀ j, IsAffineOpen (W j) := schemeFiniteCommonOpenCover_isAffineOpen U V hU hV
  have hcW : (⨆ j, W j) = ⊤ := schemeFiniteCommonOpenCover_iSup U V hcU hcV
  haveI : IsIso (openCoverCechRefinementH P U W ρ hρ q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ q).mp
      (schemeStructureFrobeniusCechRefinement_quasiIsoAt Y p hp hY U W ρ hρ hU hW hcW q)
  haveI : IsIso (openCoverCechRefinementH P V W σ hσ q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ q).mp
      (schemeStructureFrobeniusCechRefinement_quasiIsoAt Y p hp hY V W σ hσ hV hW hcW q)
  exact openCoverCechComparisonIso P U V W ρ hρ σ hσ q

end SerrePositivity.AlgebraicGeometry
