module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedRectification

/-!
概要：部分パラメータ上の実際の帰納構成から、非零境界とその比較区間を選ぶ。
方針：部分対象の入力を区間・三角形を保持して厳密化し、その比較区間を全体へ延長する。
規約：任意の区間族の高次整合性を仮定しない。使われ方：境界トレース恒等性の実構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)

/-- 指定部分の元の入力を、実三角形を保持する帰納構成で厳密化した非零境界。 -/
def kanAdjointTracedBoundary :
    B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  kanAdjointTracedComparison X Y (j ≫ φ)

/-- 非零境界の比較は、同じ部分パラメータの帰納構成で保持した実際の区間。 -/
def kanAdjointTracedBoundaryInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (j ≫ (φ ≫ kanAdjointParameterLeft X Y n))
      (kanAdjointTracedBoundary X Y φ j ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) :=
  (kanAdjointTracedEvaluationInterval X Y (j ≫ φ) n).changeEndpoints
    (Category.assoc j φ (kanAdjointParameterLeft X Y n)).symm rfl

/-- 帰納構成から得た区間を、非零境界の段調整が要求するホモトピーへ渡す。 -/
def kanAdjointTracedBoundaryHomotopy (n : ℕ) :
    KanAdjointBoundaryHomotopy X Y φ j (kanAdjointTracedBoundary X Y φ j) n :=
  (kanAdjointTracedBoundaryInterval X Y φ j n).homotopy

/-- 帰納構成の境界区間そのものを全体へ延長して作る、実際の調整済み段座標。 -/
def kanAdjointTracedBoundaryCoordinate [Mono j.right] (n : ℕ) :
    KanAdjointBoundaryCoordinate X Y φ j (kanAdjointTracedBoundary X Y φ j) n
      (kanAdjointTracedBoundaryHomotopy X Y φ j n) :=
  kanAdjointBoundaryCoordinate X Y φ j (kanAdjointTracedBoundary X Y φ j) n
    (kanAdjointTracedBoundaryHomotopy X Y φ j n)
    (kanAdjointTracedBoundaryInterval X Y φ j n).homotopy_base

/-- 選んだ調整済み段座標は、元の部分対象の帰納構成の座標へ厳密に制限される。 -/
lemma kanAdjointTracedBoundaryCoordinate_boundary [Mono j.right] (n : ℕ) :
    j ≫ (kanAdjointTracedBoundaryCoordinate X Y φ j n).coordinate =
      kanAdjointTracedBoundary X Y φ j ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n :=
  (kanAdjointTracedBoundaryCoordinate X Y φ j n).boundary

/-- 調整ホモトピーの境界は、選んだ帰納構成の比較区間全体と厳密に一致する。 -/
lemma kanAdjointTracedBoundaryCoordinate_comparison_boundary [Mono j.right] (n : ℕ) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointTracedBoundaryCoordinate X Y φ j n).comparison.h =
      (kanAdjointTracedBoundaryInterval X Y φ j n).homotopy.h :=
  (kanAdjointTracedBoundaryCoordinate X Y φ j n).comparison_boundary

end SerrePositivity.KST.Spectra.RawSpectrumMapping
