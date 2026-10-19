module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStageDifferenceTriangles
public import SerrePositivity.KST.Spectra.SpecifiedSquareDifference

/-!
概要：共有する非定数構造辺を持つ二つの正方形から、厳密な終点間の比較正方形を作る。
方針：両端に元の段比較三角形を指定し、指数写像空間で相対外ホーンを充填する。
規約：共有辺の収縮を仮定しない。使われ方：両端固定の全列区間の構造入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 元の相対正方形を、同じ共有構造辺から始まる実ホモトピーとして読む。 -/
def kanAdjointStageDifferenceFirst (n : ℕ) :
    SSet.Homotopy (kanAdjointTracedStructureInterval X Y φ n).path
      (SquareAdjustment.rightSide ≫ (kanAdjointRelativeTracedStrictStageSquare X Y φ j n).h)
    where
  h := (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (kanAdjointRelativeTracedStrictStageSquare X Y φ j n).h
  h₀ := (SquareAdjustment.flip
    (kanAdjointRelativeTracedStrictStageSquare X Y φ j n)).h₀.trans
      (kanAdjointRelativeTracedPastedSquare_start X Y φ j n)
  h₁ := (SquareAdjustment.flip (kanAdjointRelativeTracedStrictStageSquare X Y φ j n)).h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 単位正方形も、厳密に同じ共有構造辺から始まる実ホモトピーとして読む。 -/
def kanAdjointStageDifferenceSecond (n : ℕ) :
    SSet.Homotopy (kanAdjointTracedStructureInterval X Y φ n).path
      (SquareAdjustment.rightSide ≫ (kanAdjointTracedUnitStrictStageSquare X Y φ n).h) where
  h := (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (kanAdjointTracedUnitStrictStageSquare X Y φ n).h
  h₀ := (SquareAdjustment.flip (kanAdjointTracedUnitStrictStageSquare X Y φ n)).h₀.trans
    (kanAdjointTracedUnitStageSquare_start X Y φ n)
  h₁ := (SquareAdjustment.flip (kanAdjointTracedUnitStrictStageSquare X Y φ n)).h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 共通始点の二つの正方形を、同じ両端三角形全体の上で比較する相対充填。 -/
def kanAdjointStageDifferenceComposite (n : ℕ) :=
  SquareAdjustment.SpecifiedDifference.choose
    (kanAdjointStageDifferenceFirst X Y φ j n) (kanAdjointStageDifferenceSecond X Y φ n)
    (kanAdjointStageDifferenceSourceTriangle X Y φ j n)
    (kanAdjointStageDifferenceTargetTriangle X Y φ j n)
    (((SquareAdjustment.leftSide_swap _).trans
      (kanAdjointRelativeTracedStrictStageSquare X Y φ j n).h₀).trans
        (kanAdjointStageDifferenceSourceTriangle_two X Y φ j n).symm)
    (((SquareAdjustment.rightSide_swap _).trans
      (kanAdjointRelativeTracedStrictStageSquare X Y φ j n).h₁).trans
        (kanAdjointStageDifferenceTargetTriangle_two X Y φ j n).symm)
    (((SquareAdjustment.leftSide_swap _).trans
      (kanAdjointTracedUnitStrictStageSquare X Y φ n).h₀).trans
        (kanAdjointStageDifferenceSourceTriangle_one X Y φ j n).symm)
    (((SquareAdjustment.rightSide_swap _).trans
      (kanAdjointTracedUnitStrictStageSquare X Y φ n).h₁).trans
        (kanAdjointStageDifferenceTargetTriangle_one X Y φ j n).symm)

/-- 同じ上下の三角形の第二辺を比較する、厳密終点間の実構造正方形。 -/
def kanAdjointStageDifferenceSquare (n : ℕ) :=
  SquareAdjustment.SpecifiedDifference.squareHomotopy _ _ _ _
    (kanAdjointStageDifferenceComposite X Y φ j n)

/-- 比較正方形の始辺は、同じ次段の比較区間の源制限。 -/
lemma kanAdjointStageDifferenceSquare_zero (n : ℕ) :
    SSet.ι₀ ≫ (kanAdjointStageDifferenceSquare X Y φ j n).h =
      (((kanAdjointStageDifference X Y φ j (n + 1)).path).pre (X.sigma n)).path :=
  (kanAdjointStageDifferenceSquare X Y φ j n).h₀.trans
    (kanAdjointStageDifferenceSourceTriangle_zero X Y φ j n)

/-- 比較正方形の終辺は、同じ前段の比較区間の構造像。 -/
lemma kanAdjointStageDifferenceSquare_one (n : ℕ) :
    SSet.ι₁ ≫ (kanAdjointStageDifferenceSquare X Y φ j n).h =
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointStageDifference X Y φ j n).path.suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path) :=
  (kanAdjointStageDifferenceSquare X Y φ j n).h₁.trans
    (kanAdjointStageDifferenceTargetTriangle_zero X Y φ j n)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
